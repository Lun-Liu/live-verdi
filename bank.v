Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.

Definition Account := nat.
Definition Value := nat.

Inductive Name :=
| Client : Name
| Server : Name.

Inductive Msg :=
| AddMsg : Account -> Value -> Msg
| SubstractMsg : Account -> Value -> Msg
| LookupMsg : Account -> Msg
| ResponseMsg: Account -> Value -> Msg.

Inductive Input := 
| Add : Account -> Value -> Input
| Substract : Account -> Value -> Input
| Lookup : Account -> Input.

Inductive Output := Response.

Inductive Record := 
| re : Account -> Value -> Record.

Definition get_account (r : Record) : Account :=
  match r with
  | re a v => a
  end.
  
Definition get_value (r : Record) : Value :=
  match r with
  | re a v => v
  end.

(*Definition State := option (list Record).*)

(*Definition initState ( n : Name) : State:=
  match n with
    | Server => Some []
    | Client => None
  end.*)
  
Record Data := mkData { records : list Record; c : unit}.
Definition initData := mkData [] tt.
  

(* what does this mean???*)
Definition account_eq_dec : forall a a' : Account, {a = a'} + {a <> a'}.
  decide equality.
Defined.  
  
Fixpoint add_value (carrylist : list Record) (records : list Record) 
                   (a : Account) (v : Value) : list Record :=
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
  end.
  
  
Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.

Definition ClientNetHandler (m : Msg) : Handler Data := 
  match m with
    | ResponseMsg a v => nop
    | _ => nop
  end.

Definition ClientIOHandler (i : Input) : Handler Data :=
  match i with
    | Add a v => send (Server, AddMsg a v)
    | Substract a v => send (Server, SubstractMsg a v)
    | Lookup a => send (Server, LookupMsg a)
  end.

Definition ServerNetHandler( m : Msg) : Handler Data :=
  st <- get ;;
  let r := records st in
  match m with
    | AddMsg a v => put (mkData (add_value [] r a v) tt) 
    | SubstractMsg a v => put (mkData (sub_value [] r a v) tt)
    | LookupMsg a => send (Client, lookup r a)
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





