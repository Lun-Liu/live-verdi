Require Import Bank Bank_Utils.

From Verdi Require Import
  Verdi
  HandlerMonad
  LabeledNet.

From InfSeqExt Require Import
  infseq
  exteq
  classical.

From mathcomp Require Import
  ssreflect
  ssrfun
  ssrbool.

From Coq Require Import
  Classes.EquivDec
  FSets.FMapFacts
  Structures.OrderedTypeEx.

Module NatDictWF := WFacts_fun Nat_as_OT NatDict.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Bullet Behavior "Strict Subproofs".

Section Bank_Proofs.

  (*******
   * Basic lemmas on steps and traces
   *******)

  (* [SAFETY]
   * Empty trace => No change in network. [Converse cannot be proved] *)
  Lemma step_star_no_trace_no_step :
    forall net net' trace,
      step_async_star net net' trace ->
      trace = [] ->
      net = net'.
  Proof using.
    intros. invc H.
      (* net = net' *)
      - reflexivity.
      (* net -> x' -> net' *)
      - invc H1 ; invc H5.
  Qed.

  (* [SAFETY]
   * In a well-formed trace, every node must be present in Nodes. *)
  Lemma trace_well_formed :
    forall net trace trace' n io,
      step_async_star step_async_init net trace ->
      (trace = [] \/ (trace = trace' ++ [(n, io)] -> (In n Nodes))).
  Proof using.
    intros. invcs H.
    (* net = net' *)
    - intuition.
    (* net -> x' -> net' *)
    - right. intuition. apply all_Names_Nodes.
  Qed.

  (********
   * More complex properties
   ********)
  (* [SAFETY]
   * Min Value Balance : Over all traces, the returned account valuecoq
   *                     is always greater than the minimum value.
   *)
  Inductive min_value_invariant_state : State -> Prop :=
  | min_value_invariant_agent_state :
      forall astate, min_value_invariant_state (agent astate)
  | min_value_invariant_nil_state :
      min_value_invariant_state (server (NatDict.empty Value))
  | min_value_invariant_add_state :
      forall st acc val,
        min_value_invariant_state (server st) ->
        val >= minValue ->
        min_value_invariant_state (server (NatDict.add acc val st)).

  Inductive min_value_invariant_packet : packet -> Prop :=
  | min_value_invariant_passed_packet :
      forall src dst c a v,
        v >= minValue ->
        min_value_invariant_packet (mkPacket src dst (netM c (resp (PassMsg a v))))
  | min_value_invariant_other_packet :
      forall pkt,
        (not (exists c a v, (pBody pkt) = (netM c (resp (PassMsg a v))))) ->
        min_value_invariant_packet pkt.

  Definition min_value_invariant_network net :=
    min_value_invariant_state ((nwState net) Server) /\
    (forall p, In p (nwPackets net) -> min_value_invariant_packet p).

  Fixpoint min_value_invariant_outputs (outs : list output) : Prop :=
    match outs with
    | nil                        => True
    | (netO _ (Passed a v)) :: l => v >= 0 /\ (min_value_invariant_outputs l)
    | _ :: l                     => (min_value_invariant_outputs l)
    end.

  Fixpoint min_value_invariant_trace (trace : list (name * (input + list output)))
                                     : Prop :=
    match trace with
    | nil                  => True
    | (Agent, inr os) :: l => (min_value_invariant_outputs os)
                           /\ (min_value_invariant_trace l)
    | _ :: l               => (min_value_invariant_trace l)
    end.

  Lemma min_value_invariant_trace_app :
    forall tr1 tr2,
      min_value_invariant_trace tr1 /\
      min_value_invariant_trace tr2 ->
      min_value_invariant_trace (tr1 ++ tr2).
  Proof using.
    intros. induction tr1 ; intuition ; simpl in *.
    repeat break_match ; intuition.
  Qed.

  Lemma min_value_invariant_state_values :
    forall st k v,
      min_value_invariant_state (server st) ->
      NatDict.find k st = Some v ->
      v >= minValue.
  Proof using.
    intros. prep_induction H. induction H ; intros ; invcs H2.
    - apply NatDictWF.find_mapsto_iff, NatDictWF.empty_mapsto_iff in H0.
      intuition.
    - apply NatDictWF.find_mapsto_iff, NatDictWF.add_mapsto_iff in H1.
      intuition. apply NatDictWF.find_mapsto_iff in H3.
      apply (IHmin_value_invariant_state st k v) ; intuition.
  Qed.

  Lemma min_value_invariant_server_resp :
    forall msg st outs st' msgs lbl,
      min_value_invariant_state (server st) ->
      ServerNetHandler msg st = (lbl, outs, st', msgs) ->
      (min_value_invariant_state (server st') /\
        (forall d a c v,
          In (d, (netM c (resp (PassMsg a v)))) msgs ->
          v >= minValue)).
  Proof using.
    intros. split ; intros.
    (* state_values_gt_min_value st' *)
    - simplify_bank_handlers.
      (* create *)
      + apply (min_value_invariant_add_state st a minValue) ; intuition.
      (* deposit *)
      + pose proof (min_value_invariant_state_values st a v0) as Hv0. intuition.
        apply (min_value_invariant_add_state st a (v0 + v)) ; intuition.
      (* withdraw *)
      + pose proof (min_value_invariant_state_values st a v0) as Hv0. intuition.
        apply (min_value_invariant_add_state st a (v0 - v)) ; intuition.
    (* PassMsg *)
    - simplify_bank_handlers.
      + pose proof (min_value_invariant_state_values st a v1) as Hv1.
        intuition.
      + apply (min_value_invariant_state_values st' a v) ; intuition.
  Qed.

  Lemma min_value_invariant_step :
    forall net net' tr,
      min_value_invariant_network net ->
      step_async net net' tr ->
      (min_value_invariant_network net' /\ min_value_invariant_trace tr).
  Proof using.
    intros. unfold min_value_invariant_network in *. invc H0 ; intuition.
    (* NetHandler state *)
    - simpl ; intuition ; simplify_bank_handlers
                        ; apply min_value_invariant_add_state ; intuition
                        ; apply (min_value_invariant_state_values s a v0) in Heqo
                        ; intuition.
    (* NetHandler packets *)
    - simplify_bank_handlers
        ; try ( rewrite H1 in H3 ; pose proof (H3 p0)
              ; find_apply_lem_hyp in_app_iff ; intuition)
        ; try ( constructor ; intuition ; break_exists ; simpl in * ; discriminate)
        ; constructor ; find_apply_lem_hyp min_value_invariant_state_values ; intuition.
    (* NetHandler trace *)
    - simplify_bank_handlers.
    (* IOHandler state *)
    - simplify_bank_handlers.
    (* IOHandler packets *)
    - simpl in *. apply in_app_iff in H. intuition.
      simplify_bank_handlers ; constructor ; intuition ; break_exists
                             ; simpl in * ; find_inversion.
    (* IOHandler trace *)
    - simplify_bank_handlers.
  Qed.

  Theorem min_value_invariant :
    forall net tr,
      step_async_star step_async_init net tr ->
      (min_value_invariant_network net /\ min_value_invariant_trace tr).
  Proof using.
    intros. find_apply_lem_hyp refl_trans_1n_n1_trace.
    prep_induction H. induction H
                    ; intros ; simplify_bank_handlers
                    ; try (apply (min_value_invariant_step x' x'' cs') in H1 ; intuition).
    - constructor ; simpl in * ; intuition. constructor.
    - apply (min_value_invariant_trace_app cs cs'). intuition.
  Qed.

  Lemma true_in_reachable_min_value :
    true_in_reachable step_async step_async_init
                      (fun net => min_value_invariant_network net).
  Proof using.
    intro net. pose proof min_value_invariant net.
    assert (inductive_invariant step_async step_async_init min_value_invariant_network).
    - unfold inductive_invariant. split.
      + unfold min_value_invariant_network. intuition.
        apply min_value_invariant_nil_state.
      + unfold inductive. apply min_value_invariant_step.
    - find_apply_lem_hyp inductive_invariant_true_in_reachable. apply H0.
  Qed.

  (* [LIVENESS]
   * Finite Wait Time: No Agent remains waiting for ever, starting from any
                       reachable network state. *)
  Lemma Server_RespMsg_enables_Ready :
    forall id r,
      message_enables_label (mkPacket Server Agent (netM id (resp r))) Ready.
  Proof using.
    unfold message_enables_label. intros.
    find_apply_lem_hyp in_split. repeat (break_exists ; intuition).
    destruct (step_star_consistent_state net) ; try exists x1 ; intuition.
    repeat break_exists. destruct (AState_eq_dec x2 wait) ; last first.
    - repeat eexists. apply LabeledStepAsync_deliver with (xs := x) (ys := x0)
                                                          (d := agent x2) (l := []) ; eauto.
      simplify_bank_handlers; rewrite H1 in Heqd ; invcs Heqd ; intuition.
    - destruct r ; repeat eexists ;
      [ apply LabeledStepAsync_deliver with (xs := x) (ys := x0) (d := agent fail) (l := [])
      | apply LabeledStepAsync_deliver with (xs := x) (ys := x0) (d := agent pass) (l := [])]
      ; eauto ; simplify_bank_handlers ; rewrite H1 in Heqd ; invcs Heqd ; intuition
      ; (pose proof (H2 s) ; intuition).
  Qed.

  Lemma Server_RespMsg_delivered_Ready :
    forall id r,
      message_delivered_label (mkPacket Server Agent (netM id (resp r))) Ready.
  Proof using.
    unfold message_delivered_label. intros. invc H0; intuition.
    - rewrite H3 in H1.
      find_eapply_lem_hyp In_split_not_In; eauto.
      clear H2. subst. monad_unfold. simpl in *.
      handler_unfold. repeat break_match; repeat find_inversion; auto.
      apply step_star_consistent_state in H. intuition.
      apply H1 in Heqd0. inversion Heqd0.
    - find_false. apply in_app_iff; auto.
  Qed.

  Lemma RespMsg_in_network_eventually_Ready :
    forall s r id,
      initialized_eventseq s ->
      weak_fairness lb_step_async label_silent s ->
      In (mkPacket Server Agent (netM id (resp r))) (nwPackets (evt_a (hd s))) ->
      eventually (now (occurred Ready)) s.
  Proof using.
    intros. unfold initialized_eventseq in *. intuition.
    eapply message_labels_eventually_occur
          ; eauto using Server_RespMsg_enables_Ready, Server_RespMsg_delivered_Ready.
    - unfold label_silent. simpl. congruence.
    - unfold initialized_eventseq. intuition.
  Qed.

  Lemma Agent_ReqMsg_enables_Processed :
    forall id r,
      message_enables_label (mkPacket Agent Server (netM id (req r))) Processed.
  Proof using.
    unfold message_enables_label. intros.
    find_apply_lem_hyp in_split. repeat (break_exists ; intuition).
    destruct (step_star_consistent_state net) ; try exists x1 ; intuition.
  Admitted.

  Lemma Agent_ReqMsg_delivered_Processed :
    forall id r,
      message_delivered_label (mkPacket Agent Server (netM id (req r))) Processed.
  Proof using.
    unfold message_delivered_label. intros. invc H0; intuition.
    - rewrite H3 in H1.
      find_eapply_lem_hyp In_split_not_In; eauto.
      clear H2. subst. monad_unfold. simpl in *.
      handler_unfold. repeat break_match; repeat find_inversion; auto.
      apply step_star_consistent_state in H. intuition.
      apply H4 in Heqd0. inversion Heqd0.
    - find_false. apply in_app_iff; auto.
  Qed.

  Lemma ReqMsg_in_network_eventually_Processed :
    forall s r id,
      initialized_eventseq s ->
      weak_fairness lb_step_async label_silent s ->
      In (mkPacket Agent Server (netM id (req r))) (nwPackets (evt_a (hd s))) ->
      eventually (now (occurred Processed)) s.
  Proof using.
    unfold initialized_eventseq.
    intros. eapply message_labels_eventually_occur
          ; eauto using Agent_ReqMsg_enables_Processed, Agent_ReqMsg_delivered_Processed.
    - unfold label_silent. simpl. congruence.
    - unfold initialized_eventseq. intuition.
  Qed.

  Lemma Waiting_ReqMsg :
    forall s,
      initialized_eventseq s ->
      now (occurred Waiting) s ->
      exists id r, next (fun s => In (mkPacket Agent Server (netM id (req r)))
                                     (nwPackets (evt_a (hd s))))
                                     s.
  Proof using.
  Admitted.

  Lemma initialized_eventseq_invar :
    forall e s,
      initialized_eventseq (Cons e s) ->
      initialized_eventseq s.
  Proof using.
  Admitted.

  Theorem Waiting_eventually_Processed :
    forall s,
      initialized_eventseq s ->
      weak_fairness lb_step_async label_silent s ->
      now (occurred Waiting) s ->
      eventually (now (occurred Processed)) s.
  Proof using.
    intros [e s]. intuition.
    apply Waiting_ReqMsg in H1 ; intuition. break_exists.
    unfold next in *.
    apply ReqMsg_in_network_eventually_Processed in H1 ; intuition.
    - apply E_next. intuition.
    - apply (initialized_eventseq_invar e s) ; intuition.
    - apply (weak_fairness_invar H0).
  Qed.

End Bank_Proofs.