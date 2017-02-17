Require Import Bank.

From Verdi Require Import
  Verdi
  HandlerMonad
  LabeledNet.

From InfSeqExt Require Import
  infseq
  exteq.

From mathcomp Require Import
  ssreflect
  ssrfun
  ssrbool.

From Coq Require Import
  FSets.FMapFacts
  Structures.OrderedTypeEx.

Module NatDictWF := WFacts_fun Nat_as_OT NatDict.

Set Bullet Behavior "Strict Subproofs".

Section Bank_Proofs.

  (*******
   * Tactics
   *******)

  Ltac basic_unfold :=
    repeat ( unfold step_async_init,
                    unlabeled_input_handlers, unlabeled_net_handlers,
                    lb_net_handlers, lb_input_handlers,
                    net_handlers, input_handlers in *
           ; repeat break_let
           ).

  Ltac simplify_bank_handlers :=
    repeat ( monad_unfold
           ; basic_unfold
           ; unfold InitState,
                    NetHandler, AgentNetHandler, ServerNetHandler,
                    IOHandler,  AgentIOHandler,  ServerIOHandler in *
           ; repeat break_match ; simpl in * )
    ; try solve_by_inversion
    ; repeat ( repeat (find_inversion ; intuition)
             ; subst_max ; simpl in * ; intuition )
    ; repeat clean.

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
   * Error State Unreachable : Over all event-traces, ERROR never appears.
   *)
   Theorem error_unreachable :
     forall s,
       event_step_star step_async step_async_init (hd s) ->
       lb_step_execution lb_step_async s ->
       always (~_ (now (occurred ERROR))) s.
  Proof using.
    cofix c. intros. constructor.
    - unfold not_tl. intuition. admit.
    - apply c in H ; intuition. invcs H. assumption.
  Admitted.

  (* [SAFETY]
   * Min Value Balance : Over all traces, the returned account value
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

  Inductive min_value_invariant_net : network -> Prop :=
  | min_value_invariant_network :
      forall net,
        min_value_invariant_state ((nwState net) Server) ->
        (forall p, In p (nwPackets net) -> min_value_invariant_packet p) ->
        min_value_invariant_net net.

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
      min_value_invariant_net net ->
      step_async net net' tr ->
      (min_value_invariant_net net' /\ min_value_invariant_trace tr).
  Proof using.
    intros. invc H0 ; intuition.
    (* NetHandler state *)
    - apply min_value_invariant_network ; simpl ; invcs H.
      + simplify_bank_handlers ; apply min_value_invariant_add_state ; intuition.
        apply (min_value_invariant_state_values s a v0) in Heqo ; intuition.
    (* NetHandler packets *)
      + intros. basic_unfold. rewrite H1 in H3.
        apply in_app_iff in H ; invcs Heqp1 ; unfold NetHandler in H5
                              ; repeat break_match ; simpl in * ; subst_max
                              ; repeat find_inversion ; intuition
                              ; try apply in_app_iff in H2 ; try apply in_nil in H2
                              ; intuition.
        * simplify_bank_handlers.
        * apply min_value_invariant_server_resp in Heqp1 ; intuition.
          apply in_map_iff in H2. break_exists. intuition. subst_max.
          destruct x, n0, m, r ; constructor ; last 1 [ apply H4 in H6 ; intuition ]
                               ; intuition ; break_exists ; simpl in * ; find_inversion.
    (* NetHandler trace *)
    - simplify_bank_handlers.
    (* IOHandler state *)
    - apply min_value_invariant_network ; simpl ; invcs H.
      + simplify_bank_handlers.
    (* IOHandler packets *)
      + intros. apply in_app_iff in H. intuition.
        simplify_bank_handlers ; constructor ; intuition ; break_exists
                               ; simpl in * ; find_inversion.
    (* IOHandler trace *)
    - simplify_bank_handlers.
  Qed.

  Theorem min_value_invariant :
    forall net tr,
      step_async_star step_async_init net tr ->
      (min_value_invariant_net net /\ min_value_invariant_trace tr).
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
                      (fun net => min_value_invariant_net net).
  Proof using.
    intro net. pose proof min_value_invariant net.
    assert (inductive_invariant step_async step_async_init min_value_invariant_net).
    - unfold inductive_invariant. split.
      + apply min_value_invariant_network.
        * apply min_value_invariant_nil_state.
        * intuition. inversion H0.
      + unfold inductive. apply min_value_invariant_step.
    - find_apply_lem_hyp inductive_invariant_true_in_reachable. apply H0.
  Qed.

  (* [SAFETY]
   * For every account in the trace, we must have a CREATE input. *)
  Definition accounts_in_trace (trace : list (name * (input + list output)))
                               : list Account :=
    flat_map (fun n_io => match n_io with
                          | (Server, _)    => nil
                          | (Agent, inl _) => nil
                          | (Agent, inr listO) =>
                              filterMap (fun o => match o with
                                                  | netO _ (Passed a _) => Some a
                                                  | _                   => None
                                                  end)
                                        listO
                 end)
              trace.


  Theorem every_account_was_created :
    forall net trace,
      step_async_star step_async_init net trace ->
      forall a, In a (accounts_in_trace trace) ->
      exists n c, In (n, inl (netI c (Create a))) trace.
  Proof using.
  (* TODO: Do it. Do it. Do it. *)
  Admitted.

  (* [LIVENESS]
   * Finite Wait Time: No Agent remains waiting for ever, starting from any
                       reachable network state.
     FIXME: Switch to labeled network. *)
  Theorem finite_wait_time :
    forall net tr,
      step_async_star step_async_init net tr ->
      (nwState net) Agent = agent wait ->
      (exists net' tr', step_async_star net net' tr' ->
                        (nwState net') Agent <> agent wait).
  Proof using.
    intros.
  Admitted.

End Bank_Proofs.