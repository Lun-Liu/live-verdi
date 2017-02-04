Require Import
  Verdi.Verdi
  Verdi.HandlerMonad.

Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.

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

  Inductive Name := Client | Server.
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
  Definition Msg_eq_dec : forall m m' : Msg, {m = m'} + {m <> m'}.
    repeat decide equality.
  Defined.

  Inductive Input :=
  | Create    : Account -> Input
  | Deposit   : Account -> Value -> Input
  | Withdraw  : Account -> Value -> Input
  | Check     : Account -> Input.

  Inductive Output :=
  | Failed
  | Passed : Account -> Value -> Output.

  Inductive  ClientState := wait | pass | fail.
  Definition ServerState := NatDict.t Value.

  Record State := mkState {client : ClientState; server : ServerState}.
  Definition InitState (name : Name) : State :=
    mkState pass (NatDict.empty Value).

  Definition StateHandler := GenHandler (Name * Msg) State Output unit.

  Definition ClientNetHandler (m : Msg) : StateHandler :=
    state <- get ;;
    let s := server state in
    match m with
    | req  _ => nop
    | resp r => match r with
                | FailMsg     => put (mkState fail s)
                | PassMsg _ _ => put (mkState pass s)
                end
    end.

  Definition ClientIOHandler (i : Input) : StateHandler :=
    state <- get ;;
    let s := server state in (
      put (mkState wait s) ;;
      match i with
      | Create   acc     => send (Server, req (CreateMsg   acc))
      | Deposit  acc val => send (Server, req (DepositMsg  acc val))
      | Withdraw acc val => send (Server, req (WithdrawMsg acc val))
      | Check    acc     => send (Server, req (CheckMsg    acc))
      end).

  Definition ServerNetHandler (m : Msg) : StateHandler :=
    state <- get ;;
    let c := client state in
    let s := server state in
    match m with
    | resp _ => nop
    | req  r =>
        match r with
        | CreateMsg acc => 
            match NatDict.find acc s with
            | None => let val'' := 0 in (
                        put (mkState c (NatDict.add acc val'' s))
                        >> send (Client, resp (PassMsg acc val'')))
            | _    => send (Client, resp FailMsg)
            end
        | DepositMsg acc val => 
            match NatDict.find acc s with
            | Some val' => let val'' := val + val' in (
                             put (mkState c (NatDict.add acc val'' s))
                             >> send (Client, resp (PassMsg acc val'')))
            | _            => send (Client, resp FailMsg)
            end
        | WithdrawMsg acc val => 
            match NatDict.find acc s with
            | Some val' => if lt_dec val val'
                           then send (Client, resp FailMsg)
                           else let val'' := val' - val in (
                                  put (mkState c (NatDict.add acc val'' s))
                                  >> send (Client, resp (PassMsg acc val'')))
            | None      => send (Client, resp FailMsg)
            end
        | CheckMsg acc => 
            match NatDict.find acc s with
            | Some val' => send (Client, resp (PassMsg acc val'))
            | None      => send (Client, resp FailMsg)
            end
        end
    end.

  Definition ServerIOHandler (m : Input) : StateHandler := nop.

  Instance bank_base_params : BaseParams :=
  {
    data   := State ;
    input  := Input ;
    output := Output
  }.

  Definition Nodes : list Name := [Server ; Client].

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

  Definition NetHandler (dst src : Name) (m : Msg) (s : State) :=
    runGenHandler_ignore s (
      match dst with
      | Client => ClientNetHandler m
      | Server => ServerNetHandler m
      end).

  Definition IOHandler (src : Name) (i : Input) (s : State) :=
    runGenHandler_ignore s (
      match src with
      | Client => ClientIOHandler i
      | Server => ServerIOHandler i
      end).

  Instance bank_multi_params : MultiParams bank_base_params :=
  {
    name := Name ;
    name_eq_dec := Name_eq_dec;

    msg := Msg ;
    msg_eq_dec := Msg_eq_dec;

    nodes := Nodes ;
    no_dup_nodes := nodup_Nodes ;
    all_names_nodes := all_Names_Nodes;

    init_handlers := InitState ;
    net_handlers := NetHandler ;
    input_handlers := IOHandler
  }.

End Bank.
