open Bank_Coq

open Obj
open Printf
open String
open Str

(* FIXME: Need to pass client_id around to return here *)
let serializeOutput (out : output0) : int * string =
  match (magic out) with
  | Failed                 -> (0, sprintf "FailResponse")
  | Passed(account, value) -> (0, sprintf "PassResponse")

(* FIXME: Is `c` useful? *)
let deserializeInput (i : string) (c : int) : input0 option =
  let inp = String.trim i in
  let regex_2 = regexp "^\\([A-Z]+\\) +\\([0-9]+\\)$" in
  let regex_3 = regexp "^\\([A-Z]+\\) +\\([0-9]+\\) +\\([0-9]+\\)$" in
  if string_match regex_2 inp 0 then (
    match (matched_group 1 inp, matched_group 2 inp) with
    | ("CREATE", account) -> Some (Create(int_of_string account))
    | ("CHECK",  account) -> Some (Check (int_of_string account))
    | _ -> (print_endline "Invalid Input" ; None)
  ) else if string_match regex_3 inp 0 then (
    match (matched_group 1 inp, matched_group 2 inp, matched_group 3 inp) with
    | ("DEPOSIT",  account, value) -> Some (Deposit (int_of_string account,
                                                     int_of_string value))
    | ("WITHDRAW", account, value) -> Some (Withdraw(int_of_string account,
                                                     int_of_string value))
    | _ -> (print_endline "Invalid Input" ; None)
  ) else (print_endline "Invalid Input" ; None)

let serializeMsg (m : msg) : string = Marshal.to_string m []

let deserializeMsg (s : string) : msg = Marshal.from_string s 0

(* TODO: Needs changes when adding more clients / servers *)

let serializeName (n : name) : string =
  match n with
  | Server -> "server"
  | Client -> "client"

let deserializeName (s : string) : name option =
  if s = "server" then Some Server
  else if s = "client" then Some Client
  else None
