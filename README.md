# Resdet Lean verification

A Lean formalization of Resdet's paper pseudocode and its five lemmas and two
main theorems. Replicas keep independent learned logs; consensus is an explicit
contract rather than a shared log built into the protocol state.

The code follows `handle_request`, its continuation after the downstream RPC,
`handle_learn`, and `process`. The proofs have no fixed bound on replicas,
request IDs, responses, or execution length.

The fault model treats loss of leadership as a fault. A replica classified as
nonfaulty throughout its modeled incarnation therefore retains leadership.
With CG3's eventual election and the paper's request/handler progress contracts,
the proof derives leader admission and leader status at proposal time. See the
[assumption interpretation](lean/PAPER.md#assumptions-that-need-author-review).

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

Start with [Protocol.lean](lean/Resdet/Protocol.lean), then
[Assumptions.lean](lean/Resdet/Assumptions.lean),
[Safety.lean](lean/Resdet/Safety.lean), and
[Liveness.lean](lean/Resdet/Liveness.lean).

The [reading guide](lean/README.md) explains the supporting files.
[Paper correspondence](lean/PAPER.md) maps the numbered statements and records
scope differences; [proof contracts](lean/PROTOCOL.md) describes the execution
and environment interfaces.

The formalization does not prove consensus, transport, restart/recovery,
request-ID generation, or the Go implementation correct. Its exactly-once
property concerns delivery to service code, not external side effects.
