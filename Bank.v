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

  Inductive Output :=
  | Failed
  | Passed : Account -> Value -> Output.

  Definition ServerState := NatDict.t Value.
  Inductive  AgentState  := wait | pass | fail.
  Definition AState_eq_dec : forall a a' : AgentState, {a = a'} + {a <> a'}.
    decide equality.
  Defined.

  Record State := mkState {agent : AgentState; server : ServerState}.
  Definition InitState (name : Name) : State :=
    mkState pass (NatDict.empty Value).

  Definition ClientId  := String.string.
  Inductive  NetMsg    := netM : ClientId -> Msg    -> NetMsg.
  Inductive  NetInput  := netI : ClientId -> Input  -> NetInput.
  Inductive  NetOutput := netO : ClientId -> Output -> NetOutput.
  Definition NetMsg_eq_dec : forall m m' : NetMsg, {m = m'} + {m <> m'}.
    repeat decide equality.
  Defined.

  Definition StateHandler := GenHandler (Name * NetMsg) State NetOutput unit.

  Definition AgentNetHandler (nm : NetMsg) : StateHandler :=
    state <- get ;;
    let s := server state in
    let 'netM id m := nm in
    match m with
    | req  _ => nop
    | resp r => if AState_eq_dec wait (agent state) then
                  match r with
                  | FailMsg         => put (mkState fail s)
                                       >> write_output (netO id Failed)
                  | PassMsg acc val => put (mkState pass s)
                                       >> write_output (netO id (Passed acc val))
                  end
                else nop
    end.

  Definition AgentIOHandler (ni : NetInput) : StateHandler :=
    state <- get ;;
    let 'netI id i := ni in
    let s := server state in
      match i with
      | Timeout          => if AState_eq_dec fail (agent state)
                            then put (mkState fail s)
                            else nop
      | Create   acc     => put (mkState wait s)
                            ;; send (Server, netM id (req (CreateMsg   acc)))
      | Deposit  acc val => put (mkState wait s)
                            ;; send (Server, netM id (req (DepositMsg  acc val)))
      | Withdraw acc val => put (mkState wait s)
                            ;; send (Server, netM id (req (WithdrawMsg acc val)))
      | Check    acc     => put (mkState wait s)
                            ;; send (Server, netM id (req (CheckMsg    acc)))
      end.

  Definition ServerNetHandler (nm : NetMsg) : StateHandler :=
    state <- get ;;
    let c := agent state in
    let s := server state in
    let 'netM id m := nm in
    match m with
    | resp _ => nop
    | req  r =>
        match r with
        | CreateMsg acc =>
            match NatDict.find acc s with
            | None => let val'' := 0 in (
                        put (mkState c (NatDict.add acc val'' s))
                        >> send (Agent, netM id (resp (PassMsg acc val''))))
            | _    => send (Agent, netM id (resp FailMsg))
            end
        | DepositMsg acc val =>
            match NatDict.find acc s with
            | Some val' => let val'' := val + val' in (
                             put (mkState c (NatDict.add acc val'' s))
                             >> send (Agent, netM id (resp (PassMsg acc val''))))
            | _            => send (Agent, netM id (resp FailMsg))
            end
        | WithdrawMsg acc val =>
            match NatDict.find acc s with
            | Some val' => if lt_dec val val'
                           then send (Agent, netM id (resp FailMsg))
                           else let val'' := val' - val in (
                                  put (mkState c (NatDict.add acc val'' s))
                                  >> send (Agent, netM id (resp (PassMsg acc val''))))
            | None      => send (Agent, netM id (resp FailMsg))
            end
        | CheckMsg acc =>
            match NatDict.find acc s with
            | Some val' => send (Agent, netM id (resp (PassMsg acc val')))
            | None      => send (Agent, netM id (resp FailMsg))
            end
        end
    end.

  Definition ServerIOHandler (ni : NetInput) : StateHandler := nop.

  Instance bank_base_params : BaseParams :=
  {
    data   := State ;
    input  := NetInput ;
    output := NetOutput
  }.

  Definition Nodes : list Name := [Server ; Agent].

  Theorem nodup_Nodes : NoDup Nodes.
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
    runGenHandler_ignore s (
      match dst with
      | Agent  => AgentNetHandler nm
      | Server => ServerNetHandler nm
      end).

  Definition IOHandler (n : Name) (ni : NetInput) (s : State) :=
    runGenHandler_ignore s (
      match n with
      | Agent  => AgentIOHandler ni
      | Server => ServerIOHandler ni
      end).

  Instance bank_multi_params : MultiParams bank_base_params :=
  {
    name := Name ;
    name_eq_dec := Name_eq_dec;

    msg := NetMsg ;
    msg_eq_dec := NetMsg_eq_dec;

    nodes := Nodes ;
    no_dup_nodes := nodup_Nodes ;
    all_names_nodes := all_Names_Nodes;

    init_handlers := InitState ;
    net_handlers := NetHandler ;
    input_handlers := IOHandler
  }.

  Definition reboot (state : State) : State := state.
  Instance failure_params : FailureParams _ :=
  {
    reboot := reboot
  }.
End Bank.
