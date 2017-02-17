From Verdi Require Import
  Verdi
  HandlerMonad
  LabeledNet.

From Coq Require Import
  FSets.FMapList
  Structures.OrderedTypeEx.

Require String.

Module Import NatDict := FMapList.Make(Nat_as_OT).

Set Bullet Behavior "Strict Subproofs".

Section Bank.

  Definition Account := Nat_as_OT.t.
  Definition Account_eq_dec : forall a a' : Account, {a = a'} + {a <> a'}.
    decide equality.
  Defined.

  Definition Value := nat.
  Definition Value_eq_dec : forall v v' : Value, {v = v'} + {v <> v'}.
    decide equality.
  Defined.

  Definition minValue : Value := 5.

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
  | Reject
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

  Inductive Label :=
  | Ready
  | Waiting
  | Processed
  | Fulfilled
  | Nop
  | ERROR
  | Silent.
  Definition LabeledHandler (s : Type) := GenHandler (Name * NetMsg) s NetOutput Label.

  Definition ServerStateHandler := LabeledHandler ServerState.
  Definition AgentStateHandler := LabeledHandler AgentState.
  Definition StateHandler := LabeledHandler State.

  Definition AgentNetHandler (nm : NetMsg) : AgentStateHandler :=
    state <- get ;;
    let 'netM id m := nm in
    match m with
    | req  _ => ret ERROR
    | resp r =>
        if AState_eq_dec wait state then
          match r with
          | FailMsg         => put fail >> write_output (netO id Failed)
          | PassMsg acc val => put pass >> write_output (netO id (Passed acc val))
          end ;; ret Fulfilled
        else ret Nop
    end.

  Definition AgentIOHandler (ni : NetInput) : AgentStateHandler :=
    state <- get ;;
    let 'netI id i := ni in
      if AState_eq_dec wait state
      then (if Input_eq_dec i Timeout
            then put fail ;; ret Ready
            else (write_output (netO id Reject) ;; ret Nop))
      else ((if Input_eq_dec i Timeout then nop else put wait) ;;
            (match i with
             | Timeout          => nop
             | Create   acc     => send (Server, netM id (req (CreateMsg   acc)))
             | Deposit  acc val => send (Server, netM id (req (DepositMsg  acc val)))
             | Withdraw acc val => send (Server, netM id (req (WithdrawMsg acc val)))
             | Check    acc     => send (Server, netM id (req (CheckMsg    acc)))
             end) ;;
             (if Input_eq_dec i Timeout then ret Nop else ret Waiting)).

  Definition ServerNetHandler (nm : NetMsg) : ServerStateHandler :=
    state <- get ;;
    let 'netM id m := nm in
    match m with
    | resp _ => ret Nop
    | req  r =>
        match r with
        | CreateMsg acc =>
            match NatDict.find acc state with
            | None => let val'' := minValue in (
                        put (NatDict.add acc val'' state)
                        >> send (Agent, netM id (resp (PassMsg acc val''))))
            | _    => send (Agent, netM id (resp FailMsg))
            end
        | DepositMsg acc val =>
            match NatDict.find acc state with
            | Some val' => let val'' := val' + val in (
                             put (NatDict.add acc val'' state)
                             >> send (Agent, netM id (resp (PassMsg acc val''))))
            | _            => send (Agent, netM id (resp FailMsg))
            end
        | WithdrawMsg acc val =>
            match NatDict.find acc state with
            | Some val' => if lt_dec (val' - val) minValue
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
        end ;; ret Processed
    end.

  Definition ServerIOHandler (ni : NetInput) : ServerStateHandler := ret Nop.

  Global Instance bank_base_params : BaseParams :=
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
    | (Agent, agent  astate) =>
        let '(a, b, c, d) := runGenHandler astate (AgentNetHandler nm)
        in (a, b, agent c, d)
    | (Server, server sstate) =>
        let '(a, b, c, d) := runGenHandler sstate (ServerNetHandler nm)
        in (a, b, server c, d)
    | _ => (ERROR, [], s, [])
    end.

  Definition IOHandler (n : Name) (ni : NetInput) (s : State) :=
    match (n , s) with
    | (Agent, agent astate) =>
        let '(a, b, c, d) := runGenHandler astate (AgentIOHandler ni)
        in (a, b, agent c, d)
    | (Server, server sstate) =>
        let '(a, b, c, d) := runGenHandler sstate (ServerIOHandler ni)
        in (a, b, server c, d)
    | _ => (ERROR, [], s, [])
    end.

  Global Instance bank_labeled_params : LabeledMultiParams bank_base_params :=
  {
    label := Label;
    label_silent := Silent;

    lb_name := Name ;
    lb_name_eq_dec := Name_eq_dec;

    lb_msg := NetMsg ;
    lb_msg_eq_dec := NetMsg_eq_dec;

    lb_nodes := Nodes ;
    lb_no_dup_nodes := no_dup_Nodes ;
    lb_all_names_nodes := all_Names_Nodes;

    lb_init_handlers := InitState ;
    lb_net_handlers := NetHandler ;
    lb_input_handlers := IOHandler
  }.

  Global Instance bank_multi_params : MultiParams bank_base_params :=
    unlabeled_multi_params.

  (* FIXME: X_X *)
  Definition reboot (state : State) : State := state.
  Global Instance bank_failure_params : FailureParams _ :=
  {
    reboot := reboot
  }.

End Bank.
