Require Import Bank.

Require Import
  Verdi.Verdi
  Verdi.HandlerMonad.

Require Import
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx.

Module NatDictWF := WFacts_fun Nat_as_OT NatDict.

Set Bullet Behavior "Strict Subproofs".

Section Bank_Proof.

  (*******
   * Tactics
   *******)

  Ltac simplify_bank_handlers :=
    repeat ( monad_unfold
           ; unfold step_async_init, InitState,
                    NetHandler,
                    AgentNetHandler, ServerNetHandler,
                    IOHandler,
                    AgentIOHandler, ServerIOHandler in *
           ; simpl in *
           ; repeat break_match)
    ; repeat (prove_eq ; clean)
    ; subst_max
    ; simpl in *.

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
   * Min Value Balance : Over all traces, the returned account value
   *                     is always greater than the minimum value.
   *)
  Inductive min_value_invariant_state : ServerState -> Prop :=
  | min_value_invariant_nil_state :
      min_value_invariant_state (NatDict.empty Value)
  | min_value_invariant_add_state :
      forall st acc val,
        min_value_invariant_state st ->
        val >= minValue ->
        min_value_invariant_state (NatDict.add acc val st).

  Lemma min_value_invariant_state_values :
    forall st k v,
      min_value_invariant_state st ->
      NatDict.find k st = Some v ->
      v >= minValue.
  Proof using.
    intros. induction H.
    - apply NatDictWF.find_mapsto_iff, NatDictWF.empty_mapsto_iff in H0.
      intuition.
    - apply NatDictWF.find_mapsto_iff, NatDictWF.add_mapsto_iff in H0.
      intuition. apply NatDictWF.find_mapsto_iff in H3. intuition.
  Qed.

  Lemma min_value_invariant_server_resp :
    forall msg st outs st' msgs,
      min_value_invariant_state st ->
      ServerNetHandler msg st = (tt, outs, st', msgs) ->
      (min_value_invariant_state st' /\
        (forall d a c v,
          In (d, (netM c (resp (PassMsg a v)))) msgs ->
          v >= minValue)).
  Proof using.
    intros. split ; intros.
    (* state_values_gt_min_value st' *)
    - simplify_bank_handlers ; repeat find_inversion ; intuition.
      (* create *)
      + apply (min_value_invariant_add_state st a minValue) ; intuition.
      (* deposit *)
      + pose proof (min_value_invariant_state_values st a v0) as Hv0. intuition.
        apply (min_value_invariant_add_state st a (v0 + v)) ; intuition.
      (* withdraw *)
      + pose proof (min_value_invariant_state_values st a v0) as Hv0. intuition.
        apply (min_value_invariant_add_state st a (v0 - v)) ; intuition.
    (* PassMsg *)
    - simplify_bank_handlers
    ; repeat find_inversion
    ; try (destruct H1 ; try find_inversion ; intuition ; try destruct H0).
      + pose proof (min_value_invariant_state_values st a v1) as Hv1.
        intuition.
      + apply (min_value_invariant_state_values st' a v) ; intuition.
  Qed.

  Definition values_in_trace (trace : list (name * (input + list output)))
                             : list Value :=
    flat_map (fun n_io => match n_io with
                          | (Server, _)    => nil
                          | (Agent, inl _) => nil
                          | (Agent, inr listO) =>
                              filterMap (fun o => match o with
                                                  | netO _ (Passed _ v) => Some v
                                                  | _                   => None
                                                  end)
                                        listO
                 end)
              trace.

  Lemma min_value_invariant_step :
    forall st net net' st' trace,
      (nwState net) Server = server st ->
      min_value_invariant_state st ->
      step_async net net' trace ->
      (nwState net') Server = server st' ->
      (min_value_invariant_state st' /\
        (forall v, In v (values_in_trace trace) -> v >= minValue)).
  Proof using.
    intros. split.
    (* state_values_gt_min_value st' *)
    - invcs H1 ; break_if ; subst_max.
      (* NetHandler *)
      + unfold NetHandler in *. break_match.
        * invcs e.
        * break_match. invcs H4. invcs H. monad_unfold. 
          repeat break_let. invcs H4. invcs Heqp0. destruct u.
          pose proof (min_value_invariant_server_resp (pBody p) st out st' l).
          intuition.
      + simplify_bank_handlers ; try (rewrite H in H2 ; invcs H2 ; intuition).
      (* IOHandler *)
      + simplify_bank_handlers.
        * invcs H.
        * rewrite H in H5. invcs H5. intuition.
      + simplify_bank_handlers ; try (rewrite H in H2 ; invcs H2 ; intuition).
    (* forall v, In v (values_in_trace trace) -> v >= minValue *)
    - intros. invcs H1 ; break_if.
      (* NetHandler *)
      + admit.
      + apply in_nil in H3. destruct H3.
      (* IOHandler *)
      + simplify_bank_handlers ; try contradiction.
      + apply in_nil in H3. destruct H3.
  Admitted.

  Theorem min_value_invariant :
    forall net st trace,
      step_async_star step_async_init net trace ->
      (nwState net) Server = server st ->
      (min_value_invariant_state st /\
        (forall v, In v (values_in_trace trace) -> v >= minValue)).
  Proof using.
    intros.
    unfold values_in_trace in H0. split. admit.
  Admitted.

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

  (* [SAFETY]
   * For every account in the trace, we must have a CREATE input. *)
  Theorem every_account_was_created :
    forall net trace,
      step_async_star step_async_init net trace ->
      forall a, In a (accounts_in_trace trace) ->
      exists n c, In (n, inl (netI c (Create a))) trace.
  Proof using.
  (* TODO: Do it. Do it. Do it. *)
  Admitted.

  (* [SAFETY]
   * Trace Correctness : Simulate the trace on an interpreter and prove that
   *                     we get equivalent behaviour on the distributed system.
   *)

(*  Definition operate (op : Input) (curr : option Value) :=
    match op with
    | Timeout          => (curr, curr)
    | Create   acc     => (curr, curr)
    | Deposit  acc val => (curr, curr)
    | Withdraw acc val => (curr, curr)
    | Check    acc     => (curr, curr)
    end.

  Fixpoint interpret (acc : Account) (ops : list Input) (init : option Value) :=
    match ops with
    | [] => (init, init)
    | _  => (init, init)
    end.
*)

End Bank_Proof.