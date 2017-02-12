open Bank_Coq

open Printf
open String
open Str
open Util

let invalidInputMessage (c : clientId) : netInput option =
  print_endline ("[!] INVALID INPUT from " ^ (string_of_char_list c)) ; None

let serializeOutput (out : netOutput) : clientId * string =
  match (Obj.magic out) with
  | NetO(client, Reject)
      -> (client, sprintf "REJECTED\n")
  | NetO(client, Failed)
      -> (client, sprintf "FAIL\n")
  | NetO(client, Passed (account, value))
      -> (client, sprintf "PASS: %d %d\n" account value)

let deserializeInput (i : string) (c : clientId) : netInput option =
  let inp = String.trim i in
  if inp = "TIMEOUT" then Some (NetI (c, Timeout)) else
  let regex_2 = regexp "^\\([A-Z]+\\) +\\([0-9]+\\)$" in
  let regex_3 = regexp "^\\([A-Z]+\\) +\\([0-9]+\\) +\\([0-9]+\\)$" in
  if string_match regex_2 inp 0 then (
    match (matched_group 1 inp, matched_group 2 inp) with
    | ("CREATE", account) -> Some (NetI (c, Create (int_of_string account)))
    | ("CHECK",  account) -> Some (NetI (c, Check (int_of_string account)))
    | _ -> (print_endline "Invalid Input" ; None)
  ) else if string_match regex_3 inp 0 then (
    match (matched_group 1 inp, matched_group 2 inp, matched_group 3 inp) with
    | ("DEPOSIT",  account, value)
        -> Some (NetI (c, Deposit (int_of_string account, int_of_string value)))
    | ("WITHDRAW", account, value)
        -> Some (NetI (c, Withdraw(int_of_string account, int_of_string value)))
    | _ -> invalidInputMessage c
  ) else invalidInputMessage c

let serializeMsg (m : netMsg) : string = Marshal.to_string m []

let deserializeMsg (s : string) : netMsg = Marshal.from_string s 0

(* For debugging *)

type direction = Send | Recv

let serializeReqHumanReadable (rm : reqMsg) : string =
  match rm with
  | CreateMsg   a    -> sprintf "CREATE %d"      a
  | DepositMsg (a,v) -> sprintf "DEPOSIT %d %d"  a v
  | WithdrawMsg(a,v) -> sprintf "WITHDRAW %d %d" a v
  | CheckMsg    a    -> sprintf "CHECK %d"       a

let serializeRespHumanReadable (rm : respMsg) : string =
  match rm with
  | FailMsg      -> "FAIL"
  | PassMsg(a,v) -> sprintf "PASS %d %d" a v

let serializeMsgHumanReadable (nm : netMsg) : (string * string) =
  let NetM (id, m) = nm in
    ((string_of_char_list id),
     (match m with Req rm  -> serializeReqHumanReadable rm
                 | Resp rm -> serializeRespHumanReadable rm))

let dbgSerializeState (s : state) : string =
  match s with
  | Agent0 Wait -> "A Wait"
  | Agent0 Pass -> "A Pass"
  | Agent0 Fail -> "A Fail"
  | Server0 _   -> "S"

let dbgSerializeComm (d : direction) (s : state) ((n , m) : name * netMsg) =
  let (id, sm) = serializeMsgHumanReadable m in
    print_endline ("  " ^ id ^ " [" ^ (dbgSerializeState s) ^ "]"
                        ^ (if d = Send then " > " else " < ") ^ sm)

let serializeInputHumanReadable (ni : netInput) : (string * string) =
  let NetI (id, i) = ni in
    ((string_of_char_list id),
     (match i with
      | Timeout       -> "TIMEOUT"
      | Create a      -> sprintf "CREATE %d"      a
      | Deposit(a,v)  -> sprintf "DEPOSIT %d %d"  a v
      | Withdraw(a,v) -> sprintf "WITHDRAW %d %d" a v
      | Check(a)      -> sprintf "CHECK %d"       a))

let dbgSerializeInput (s : state) (i : netInput) =
  let (id, si) = serializeInputHumanReadable i in
    print_endline ("  " ^ id ^ " [" ^ (dbgSerializeState s) ^ "]" ^ " >>> " ^ si)

let dbgSerializeTimeout (s : state) = ()
