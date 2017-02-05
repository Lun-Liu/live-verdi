open Bank_Coq

open Obj

module type BankParams = sig
  val debug : bool
end

module DebugParams = struct
  let debug = true
end

module BankArrangement (P : BankParams) = struct
  type client_id = int
  type name = Bank_Coq.name
  type msg = Bank_Coq.msg
  type state = Bank_Coq.state
  type input = Bank_Coq.input0
  type output = Bank_Coq.output0

  type res = (output list * state) * ((name * msg) list)
  type task_handler = name -> state -> res
  type timeout_setter = name -> state -> float

  let systemName = "Distributed Banking System"
  let init (n : name) = magic (bank_multi_params.init_handlers (magic n))

  let handleIO (n : name) (i : input) (s : state) =
    magic (bank_multi_params.input_handlers (magic n) (magic i) (magic s))
  let handleNet (d : name) (n : name) (m : msg) (s : state) =
    magic (bank_multi_params.net_handlers (magic d) (magic n) (magic m) (magic s))

  let deserializeMsg = Bank_Serialization.deserializeMsg
  let serializeMsg = Bank_Serialization.serializeMsg
  let deserializeInput = Bank_Serialization.deserializeInput
  let serializeOutput = Bank_Serialization.serializeOutput
  let deserializeName = Bank_Serialization.deserializeName
  let serializeName = Bank_Serialization.serializeName

  let failMsg = Some (Resp FailMsg)
  let newMsg = None

  let debug = P.debug
  let debugRecv (s : state) ((n , m) : name * msg) = ()
  let debugSend (s : state) ((n , m) : name * msg) = ()
  let debugTimeout (s : state) = ()
  let debugInput (s : state) (i : input) = ()

  let createClientId () = let upper_bound = 1073741823 in Random.int upper_bound
  let serializeClientId = string_of_int

  (* FIXME: Timeouts are arbitrary right now *)
  let setTimeout _ s = Random.float 0.1
  let handleTimeout (n : name) (s : state) =
    magic bank_multi_params.input_handlers (magic n) (magic Timeout) (magic s)
  let timeoutTasks = []
end
