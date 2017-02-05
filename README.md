# Distributed Banking System

A simple project to experiment with proving liveness properties in [Verdi][verdi].

## Extraction & Execution

- `make` in the root directory to compile the proofs _and_ extract executable code
- Running `Bank.native`:

```shell-script
# Server listening for input on port 8100, talking to Client on 9100
$ ./Bank.native -me 0 -port 8100 -node 0,localhost:9100 -node 1,localhost:9101

# Client listening for input on port 8101, talking to Server on 9101
$ ./Bank.native -me 1 -port 8101 -node 0,localhost:9100 -node 1,localhost:9101
```

[verdi]: https://github.com/uwplse/verdi
