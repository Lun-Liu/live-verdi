open Bank_Coq
open Bank_Serialization

open Obj
open Printf
open Util

module type BankParams = sig
  val debug : bool
end

module DebugParams = struct
  let debug = true
end

module DefaultParams = struct
  let debug = false
end

module BankArrangement (P : BankParams) = struct
  type name = Bank_Coq.name
  type msg = Bank_Coq.netMsg
  type state = Bank_Coq.state
  type input = Bank_Coq.netInput
  type output = Bank_Coq.netOutput
  type res = (output list * state) * ((name * msg) list)

  let reboot = Bank_Coq.reboot
  let systemName = "Distributed Banking System"
  let init (n : name) = magic (bank_multi_params.init_handlers (magic n))

  type client_id = Bank_Coq.clientId
  let createClientId () = char_list_of_string (Uuidm.to_string (Uuidm.create `V4))
  let serializeClientId (c : char list) = string_of_char_list c

  let handleIO (n : name) (i : input) (s : state) =
    magic (bank_multi_params.input_handlers (magic n) (magic i) (magic s))
  let handleNet (d : name) (n : name) (m : msg) (s : state) =
    magic (bank_multi_params.net_handlers (magic d) (magic n) (magic m) (magic s))

  let deserializeMsg = Bank_Serialization.deserializeMsg
  let serializeMsg = Bank_Serialization.serializeMsg
  let deserializeInput = Bank_Serialization.deserializeInput
  let serializeOutput = Bank_Serialization.serializeOutput

  let debug = P.debug
  let debugRecv = dbgSerializeComm Recv
  let debugSend = dbgSerializeComm Send
  let debugTimeout = dbgSerializeTimeout
  let debugInput = dbgSerializeInput

  (* FIXME: Timeouts are arbitrary right now *)
  let setTimeout _ _ = Random.float 0.5
  let handleTimeout (n : name) (s : state) =
    magic (bank_multi_params.input_handlers
               (magic n) (magic (NetI ([], Timeout))) (magic s))
end
