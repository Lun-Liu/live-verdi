open Bank_Coq

open Printf
open String
open Str
open Util

let invalidInputMessage (c : netId) : netInput option =
  print_endline ("[!] INVALID INPUT from " ^ (string_of_char_list c)) ; None

let serializeOutput (out : netOutput) : char list * string =
  match (Obj.magic out) with
  | NetO(client, Failed)
      -> (client, sprintf "FAIL\n")
  | NetO(client, Passed (account, value))
      -> (client, sprintf "PASS: %d %d\n" account value)

let deserializeInput (i : string) (c : netId) : netInput option =
  let inp = String.trim i in
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
  ""

let serializeRespHumanReadable (rm : respMsg) : string =
  ""

let serializeMsgHumanReadable (nm : netMsg) : (string * string) =
  let NetM (id, m) = nm in
    ((string_of_char_list id),
     (match m with Req rm  -> serializeReqHumanReadable rm
                 | Resp rm -> serializeRespHumanReadable rm))

let dbgSerializeComm (d : direction) (s : state) ((n , m) : name * netMsg) =
  let (id, sm) = serializeMsgHumanReadable m in
    print_endline ("  " ^ id ^ (if d = Send then " < " else " > ") ^ sm)

let dbgSerializeInput (s : state) (i : netInput) = ()

let dbgSerializeTimeout (s : state) = ()
