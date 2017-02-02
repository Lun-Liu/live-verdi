Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.

Require Import
  Coq.FSets.FMapList
  Coq.Structures.OrderedTypeEx.

Module Import M := FMapList.Make(Nat_as_OT).

Definition Account := nat.
Definition Value := nat.

Inductive Name :=
| Client : Name
| Server : Name.

Inductive Msg :=
| CreateMsg : Account -> Msg
| AddMsg : Account -> Value -> Msg
| SubstractMsg : Account -> Value -> Msg
| LookupMsg : Account -> Msg
| SucceedMsg : Msg
| FailMsg : Msg
| ResponseMsg: Account -> Value -> Msg.

Inductive Input := 
| Create : Account -> Input
| Add : Account -> Value -> Input
| Substract : Account -> Value -> Input
| Lookup : Account -> Input.

Inductive Output := Response.

(*No need for those, use FMap library instead*)

(*Inductive Record := 
| re : Account -> Value -> Record.

Definition get_account (r : Record) : Account :=
  match r with
  | re a v => a
  end.
  
Definition get_value (r : Record) : Value :=
  match r with
  | re a v => v
  end.*)

(*Definition State := option (list Record).*)

(*Definition initState ( n : Name) : State:=
  match n with
    | Server => Some []
    | Client => None
  end.*)
  
  
(*Fixpoint add_value (carrylist : list Record) (records : list Record) 
                   (a : Account) (v : Value) : Handler Data :=
  match records with
  | x::l1 => if (account_eq_dec (get_account x) a) 
             then (app carrylist (re (get_account x) ((get_value x) + v)::l1))
             else add_value (app carrylist [x]) l1 a v
  | [] => app carrylist [re a v]
  end.


Fixpoint sub_value (carrylist : list Record) (records : list Record) 
                   (a : Account) (v : Value) : list Record :=
  match records with
  | x::l1 => if (account_eq_dec (get_account x) a) 
             then (app carrylist (re (get_account x) ((get_value x) - v)::l1))
             else sub_value (app carrylist [x]) l1 a v
  | [] => app carrylist [re a (0-v)]
  end.
  
Fixpoint lookup (records : list Record) (a : Account) : Msg :=
  match records with
  | x::l1 => if (account_eq_dec (get_account x) a) 
             then ResponseMsg (get_account x) (get_value x) 
             else lookup l1 a 
  | [] => ResponseMsg 0 0
  end.*)
  
  
Inductive ClientState := init | wait | succeeded | failed.
  
Record Data := mkData { records : M.t nat; c : ClientState}.
Definition initData := mkData (M.empty nat) init.
  

Definition account_eq_dec : forall a a' : Account, {a = a'} + {a <> a'}.
  decide equality.
Defined.  

Definition value_eq_dec : forall v v' : Value, {v = v'} + {v <> v'}.
  decide equality.
Defined.  

  
Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

Definition ClientNetHandler (m : Msg) : Handler Data := 
  st <- get ;;
  let r := records st in
  match m with
    | SucceedMsg => put (mkData r succeeded)
    | FailMsg => put (mkData r failed)
    | ResponseMsg a v => put (mkData r succeeded)
    | _ => nop
  end.

Definition ClientIOHandler (i : Input) : Handler Data :=
  st <- get ;;
  let r  := records st in
  put (mkData r wait);;
  match i with
    | Create a  => send (Server, CreateMsg a) 
    | Add a v => send (Server, AddMsg a v)
    | Substract a v => send (Server, SubstractMsg a v)
    | Lookup a => send (Server, LookupMsg a)
  end.


Definition ServerNetHandler( m : Msg) : Handler Data :=
  st <- get ;;
  let r := records st in
  let c := c st in
  match m with
    | CreateMsg a => 
      match M.find a r with
      | Some v => send (Client, FailMsg)
      | None => put (mkData (M.add a 0 r) c) >> send (Client, SucceedMsg)
      end
    | AddMsg a v => 
      match M.find a r with
      | Some v' => put (mkData (M.add a (v+v') r) c) >> send (Client, SucceedMsg)
      | None => send (Client, FailMsg)
      end
    | SubstractMsg a v => 
      match M.find a r with
      | Some v' => if lt_dec v v' then send (Client, FailMsg)
                   else put (mkData (M.add a (v-v') r) c) >> send (Client, SucceedMsg)
      | None => send (Client, FailMsg)
      end
    | LookupMsg a => 
      match M.find a r with
      | Some v' => send (Client, ResponseMsg a v')
      | None => send (Client, FailMsg)
      end
    | _ => nop
  end.

Definition ServerIOHandler (m : Input) : Handler Data := nop.

Definition NetHandler (nm src : Name) (m : Msg) : Handler Data :=
  match nm with
    | Client => ClientNetHandler m
    | Server   => ServerNetHandler m
  end.

Definition InputHandler (nm : Name) (i : Input) : Handler Data :=
  match nm with
    | Client => ClientIOHandler i
    | Server   => ServerIOHandler i
  end.





