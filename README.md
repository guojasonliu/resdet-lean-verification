# Resdet Lean verification

A Lean formalization of Resdet's paper pseudocode and its five lemmas and two
main theorems. Replicas keep independent learned logs; consensus is an explicit
contract rather than a shared log built into the protocol state.

The code follows `handle_request`, its continuation after the downstream RPC,
`handle_learn`, and `process`. The proofs have no fixed bound on replicas,
request IDs, responses, or execution length.

Each retry can propose its own response, even if the replica loses leadership
during the downstream call. Under CG3(2), if proposals keep arriving for a
request ID, consensus eventually agrees on one of them. Each replica delivers
the response at the first agreed index for that ID.

## Check

The project uses Lean 4.24.0 and its bundled standard library, without external
Lean packages:

```sh
make fetch-lean    # one-time local toolchain installation
make check-lean    # compile proofs/examples and audit their axiom dependencies
```

An existing toolchain can be selected with
`LEAN_BIN=/absolute/path/to/bin make check-lean`.

Warnings are errors. The audit permits only `propext`, `Quot.sound`, and
`Classical.choice`; unfinished proofs and extra axioms are rejected.
`lake build` alone does not run that audit.

## Review

Start with the [Resdet pseudocode](lean/Resdet/resdet.lean), then read the
[consensus guarantees](lean/Resdet/consensus_assumptions.lean) and
[liveness assumptions](lean/Resdet/liveness_assumptions.lean).
The [safety proofs](lean/Resdet/safety.lean) and
[liveness proofs](lean/Resdet/liveness.lean) follow the paper’s lemma numbering.

The [reading guide](lean/README.md) explains the supporting files.
[Paper correspondence](lean/PAPER.md) maps the numbered statements and records
scope differences; [proof contracts](lean/PROTOCOL.md) describes the execution
and environment interfaces.

The formalization does not prove consensus, transport, restart/recovery,
request-ID generation, or the Go implementation correct. Its exactly-once
property concerns delivery to service code, not external side effects.
