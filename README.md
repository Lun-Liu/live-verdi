# Distributed Banking System

A simple project to experiment with proving liveness properties in
[Verdi][verdi].

It spawns a banking server which keeps the account records, and a trusted agent
(equivalent of an ATM) to which clients can talk to, for making transactions.

## Requirements

Proofs:
- `verdi`
- `coq`
- `coq-mathcomp-ssreflect`

Executable:
- `verdi-runtime`
- `verdi`
- `coq`
- `ocamlbuild`
- `ocamlfind`
- `uuidm`

(All of the above are `opam install`-able.)

## Extraction & Execution

- `make` in the root directory to compile the proofs _and_ extract executable code
- Running the cluster using `Bank.native`:

```shell-script
# Server listening for input on port 8100, talking to agent on 9100
$ ./bank.bin -me 0 -port 8100 -node 0,localhost:9100 -node 1,localhost:9101

# Agent listening for input on port 8101, talking to Server on 9101
$ ./bank.bin -me 1 -port 8101 -node 0,localhost:9100 -node 1,localhost:9101
```

- User interactions: making transactions using the agent can be made by connecting
  to the port the agent is listening on. For example:

```shell-script
# Connect to agent
$ socat tcp:localhost:8101 -
CHECK 1001
FAIL
CREATE 1001
PASS 1001 0
DEPOSIT 1001 10
PASS 1001 10
CHECK 1001
PASS 1001 10
...
```

(or use `make bank.d.byte` for a debug-build)

[verdi]: https://github.com/uwplse/verdi
