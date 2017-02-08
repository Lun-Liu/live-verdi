Require Import Bank.

Require Import
  Verdi.Verdi
  Verdi.HandlerMonad.

Set Bullet Behavior "Strict Subproofs".

Section Bank_Proof.

  (*******
   * Tactics
   *******)

  (* Repeated unfolding of all handler monads *)
  Ltac bank_handlers_unfold :=
    repeat (monad_unfold
           ; unfold InitState,
                    NetHandler,
                    AgentNetHandler, ServerNetHandler,
                    IOHandler,
                    AgentIOHandler, ServerIOHandler in *).

  (*******
   * Basic lemmas on steps and traces
   *******)

  (* Empty trace => No change in network.
   * [Converse cannot be proved] *)
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

  (* In a well-formed trace,
   * every node must be present in Nodes. *)
  Lemma trace_well_formed :
    forall net trace trace' n io,
      step_async_star step_async_init net trace ->
      (trace = [] \/ (trace = trace' ++ [(n, io)] -> (List.In n Nodes))).
  Proof using.
    intros. invcs H.
    (* net = net' *)
    - intuition.
    (* net -> x' -> net' *)
    - right. intuition. apply all_Names_Nodes.
  Qed.

  Definition trace_values (trace : list (name * (input + list output)))
                          : list Value :=
    flat_map (fun n_io => match n_io with
                          | (Server, _)    => nil
                          | (Agent, inl _) => nil
                          | (Agent, inr listO) =>
                              filterMap (fun o => match o with
                                                  | netO _ Failed => None
                                                  | netO _ (Passed _ v) => Some v
                                                  end)
                                        listO
                 end)
              trace.

  (* [SAFETY]
   * No Negative Value : Over all traces, the returned account value
   *                     is always non-negative.
   *)
  Theorem no_negative_value :
    forall net trace,
      step_async_star step_async_init net trace ->
      forall v, List.In v (trace_values trace) -> v >= 0.
  Proof using.
    intros net trace H_network_step_star v H_v_in_trace.
    unfold trace_values in H_v_in_trace.
    apply in_flat_map in H_v_in_trace.
  Admitted.

(* 
  SAFETY for STATES, no need now

  Definition valid_values (m : ServerState) : Prop := 
    forall acc v,
      NatDict.find acc m = Some v ->
      v >= 0.

  Definition bank_correct (sigma : Name -> State) : Prop :=
    match (sigma Server) with
    | agent  _      => False
    | server sstate => valid_values sstate
    end.

  Lemma bank_correct_init :
    bank_correct init_handlers.
  Proof using.
    simpl. discriminate.
  Qed.
  
  Definition timeout_case (i : NetInput) (out : list NetOutput) (st : State) (st' : State) (ms : list (Name * NetMsg)) :=
  match st with
  | server ss => False
  | agent _ => exists cid, i = netI cid (Timeout) /\ out = [] /\ ms = []
  end.
  
  Definition create_case (i : NetInput) (out : list NetOutput) (st : State) (st' : State) (ms : list (Name * NetMsg)) :=
  match st with
  | server ss => False
  | agent _ => exists a cid, i = netI cid (Create a) /\ out = [] /\ ms = [(Server, netM cid (req (CreateMsg a)))]
  end.
  
  Definition deposit_case (i : NetInput) (out : list NetOutput) (st : State) (st' : State) (ms : list (Name * NetMsg)) :=
  match st with
  | server ss => False
  | agent _ => exists a v cid, i = netI cid (Deposit a v) /\ out = []  /\ ms = [(Server, netM cid (req (DepositMsg a v)))]
  end.
  
  Definition withdraw_case (i : NetInput) (out : list NetOutput) (st : State) (st' : State) (ms : list (Name * NetMsg)) :=
  match st with
  | server ss => False
  | agent _ => exists a v cid, i = netI cid (Withdraw a v) /\ out = [] /\ ms = [(Server, netM cid (req (WithdrawMsg a v)))]
  end.

  Definition check_case (i : NetInput) (out : list NetOutput) (st : State) (st' : State) (ms : list (Name * NetMsg)) :=
  match st with
  | server ss => False
  | agent _ => exists a cid, i = netI cid (Check a) /\ out = [] /\ ms = [(Server, netM cid (req (CheckMsg a)))]
  end.

  Ltac handler_unfold :=
    repeat (monad_unfold; unfold NetHandler,
                                 IOHandler,
                                 ServerNetHandler,
                                 AgentNetHandler,
                                 AgentIOHandler,
                                 ServerIOHandler in .
  
  Lemma IOHandler_cases:
  forall name input state netout state' ms,
    IOHandler name input state = (netout, state', ms) ->
    (name = Agent /\ (timeout_case input netout state state' ms \/ create_case input netout state state' ms \/ deposit_case input netout state state' ms \/ withdraw_case input netout state state' ms \/ check_case input netout state state' ms)) \/ (netout = [] /\ state = state' /\ ms = []). 
  Proof.
  handler_unfold. intros.
  repeat break_match;
  repeat tuple_inversion;
  [left|left|left|left|left|left|left|right|right|right]; 
  try intuition.
  - left. unfold timeout_case. repeat eexists.
  - right. left. unfold create_case. repeat eexists.
  - right. right. left. unfold deposit_case. repeat eexists.
  - right. right. right. left. unfold withdraw_case. repeat eexists.
  - repeat (try right). unfold check_case. repeat eexists.
Qed.

  Lemma bank_correct_io_handlers :
    forall name input sigma st' netout ms,
      IOHandler name input (sigma name) = (netout, st', ms) ->
      bank_correct sigma ->
      bank_correct (update name_eq_dec sigma name st').
  Proof. 
  Admitted.
   
  Lemma bank_correct_net_handlers :
    forall p sigma st' out ms,
      NetHandler (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (out, st', ms) ->
      bank_correct sigma ->
      bank_correct (update name_eq_dec sigma (pDst p) st').
  Proof.
  Admitted.
  
  Theorem true_in_reachable_bank_correct :
  true_in_reachable step_async step_async_init (fun net => bank_correct (nwState net)).
  Proof.
  Admitted.*)

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