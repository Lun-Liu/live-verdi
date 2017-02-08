Require Import
  Verdi.Verdi
  Verdi.HandlerMonad.

Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.

Require String.

Module Import NatDict := FMapList.Make(Nat_as_OT).

Section Bank.
  Definition Account := Nat_as_OT.t.
  Definition Account_eq_dec : forall a a' : Account, {a = a'} + {a <> a'}.
    decide equality.
  Defined.

  Definition Value := nat.
  Definition Value_eq_dec : forall v v' : Value, {v = v'} + {v <> v'}.
    decide equality.
  Defined.

  Inductive Name := Agent | Server.
  Definition Name_eq_dec : forall n n' : Name, {n = n'} + {n <> n'}.
    decide equality.
  Defined.

  Inductive ReqMsg :=
  | CreateMsg   : Account -> ReqMsg
  | DepositMsg  : Account -> Value  -> ReqMsg
  | WithdrawMsg : Account -> Value  -> ReqMsg
  | CheckMsg    : Account -> ReqMsg.

  Inductive RespMsg :=
  | FailMsg
  | PassMsg : Account -> Value -> RespMsg.

  Inductive Msg :=
  | req  : ReqMsg  -> Msg
  | resp : RespMsg -> Msg.

  Inductive Input :=
  | Timeout
  | Create   : Account -> Input
  | Deposit  : Account -> Value -> Input
  | Withdraw : Account -> Value -> Input
  | Check    : Account -> Input.
  Definition Input_eq_dec : forall i i' : Input, {i = i'} + {i <> i'}.
    repeat decide equality.
  Defined.

  Inductive Output :=
  | Failed
  | Passed : Account -> Value -> Output.

  Definition ServerState := NatDict.t Value.
  Inductive  AgentState  := wait | pass | fail.
  Definition AState_eq_dec : forall a a' : AgentState, {a = a'} + {a <> a'}.
    decide equality.
  Defined.

  Inductive State :=
  | agent  : AgentState  -> State
  | server : ServerState -> State.
  Definition InitState (name : Name) : State :=
    match name with
    | Agent  => agent  pass
    | Server => server (NatDict.empty Value)
    end.

  Definition ClientId  := String.string.
  Inductive  NetMsg    := netM : ClientId -> Msg    -> NetMsg.
  Inductive  NetInput  := netI : ClientId -> Input  -> NetInput.
  Inductive  NetOutput := netO : ClientId -> Output -> NetOutput.
  Definition NetMsg_eq_dec : forall m m' : NetMsg, {m = m'} + {m <> m'}.
    repeat decide equality.
  Defined.

  Definition MakeHandler (s : Type) :=
    GenHandler (Name * NetMsg) s NetOutput unit.
  Definition AgentStateHandler := MakeHandler AgentState.
  Definition ServerStateHandler := MakeHandler ServerState.
  Definition StateHandler := MakeHandler State.

  Definition AgentNetHandler (nm : NetMsg) : AgentStateHandler :=
    state <- get ;;
    let 'netM id m := nm in
    match m with
    | req  _ => nop
    | resp r =>
        if AState_eq_dec wait state then
          match r with
          | FailMsg         => put fail >> write_output (netO id Failed)
          | PassMsg acc val => put pass >> write_output (netO id (Passed acc val))
          end
        else nop
    end.

  Definition AgentIOHandler (ni : NetInput) : AgentStateHandler :=
    state <- get ;;
    let 'netI id i := ni in
      if Input_eq_dec i Timeout then nop else put wait ;;
      match i with
      | Timeout          => if AState_eq_dec fail state then nop else put fail
      | Create   acc     => send (Server, netM id (req (CreateMsg   acc)))
      | Deposit  acc val => send (Server, netM id (req (DepositMsg  acc val)))
      | Withdraw acc val => send (Server, netM id (req (WithdrawMsg acc val)))
      | Check    acc     => send (Server, netM id (req (CheckMsg    acc)))
      end.

  Definition ServerNetHandler (nm : NetMsg) : ServerStateHandler :=
    state <- get ;;
    let 'netM id m := nm in
    match m with
    | resp _ => nop
    | req  r =>
        match r with
        | CreateMsg acc =>
            match NatDict.find acc state with
            | None => let val'' := 0 in (
                        put (NatDict.add acc val'' state)
                        >> send (Agent, netM id (resp (PassMsg acc val''))))
            | _    => send (Agent, netM id (resp FailMsg))
            end
        | DepositMsg acc val =>
            match NatDict.find acc state with
            | Some val' => let val'' := val + val' in (
                             put (NatDict.add acc val'' state)
                             >> send (Agent, netM id (resp (PassMsg acc val''))))
            | _            => send (Agent, netM id (resp FailMsg))
            end
        | WithdrawMsg acc val =>
            match NatDict.find acc state with
            | Some val' => if lt_dec val val'
                           then send (Agent, netM id (resp FailMsg))
                           else let val'' := val' - val in (
                                  put (NatDict.add acc val'' state)
                                  >> send (Agent, netM id (resp (PassMsg acc val''))))
            | None      => send (Agent, netM id (resp FailMsg))
            end
        | CheckMsg acc =>
            match NatDict.find acc state with
            | Some val' => send (Agent, netM id (resp (PassMsg acc val')))
            | None      => send (Agent, netM id (resp FailMsg))
            end
        end
    end.

  Definition ServerIOHandler (ni : NetInput) : ServerStateHandler := nop.

  Instance bank_base_params : BaseParams :=
  {
    data   := State ;
    input  := NetInput ;
    output := NetOutput
  }.

  Definition Nodes : list Name := [Server ; Agent].

  Theorem no_dup_Nodes : NoDup Nodes.
  Proof using.
    unfold Nodes. apply NoDup_cons ; simpl.
    - easy'.
    - apply NoDup_cons.
      + easy.
      + apply NoDup_nil.
  Qed.

  Theorem all_Names_Nodes : forall n : Name, List.In n Nodes.
  Proof using.
    unfold Nodes, List.In. destruct n ; auto.
  Qed.

  Definition NetHandler (dst src : Name) (nm : NetMsg) (s : State) :=
    match (dst , s) with
    | (Agent  , agent  astate) =>
        let '(a,b,c) := runGenHandler_ignore astate (AgentNetHandler nm)
        in (a, agent b, c)
    | (Server , server sstate) =>
        let '(a,b,c) := runGenHandler_ignore sstate (ServerNetHandler nm)
        in (a, server b, c)
    | _ => runGenHandler_ignore s nop
    end.

  Definition IOHandler (n : Name) (ni : NetInput) (s : State) :=
    match (n , s) with
    | (Agent  , agent  astate) =>
        let '(a,b,c) := runGenHandler_ignore astate (AgentIOHandler ni)
        in (a, agent b, c)
    | (Server , server sstate) =>
        let '(a,b,c) := runGenHandler_ignore sstate (ServerIOHandler ni)
        in (a, server b, c)
    | _ => runGenHandler_ignore s nop
    end.

  Instance bank_multi_params : MultiParams bank_base_params :=
  {
    name := Name ;
    name_eq_dec := Name_eq_dec;

    msg := NetMsg ;
    msg_eq_dec := NetMsg_eq_dec;

    nodes := Nodes ;
    no_dup_nodes := no_dup_Nodes ;
    all_names_nodes := all_Names_Nodes;

    init_handlers := InitState ;
    net_handlers := NetHandler ;
    input_handlers := IOHandler
  }.

  (* FIXME: X_X *)
  Definition reboot (state : State) : State := state.
  Instance failure_params : FailureParams _ :=
  {
    reboot := reboot
  }.

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

  (* Basic lemmas on stepping*)

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

End Bank.