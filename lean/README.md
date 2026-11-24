# Reading the Lean proof

Start with the request and delivery handlers, then read the numbered proofs
beside Sections 4 and 5 of the paper.

| File | Paper correspondence |
| --- | --- |
| [resdet.lean](Resdet/resdet.lean) | Section 4. Replica state, handlers, and execution steps. |
| [consensus_assumptions.lean](Resdet/consensus_assumptions.lean) | The committed-entry callback interface and CG1–CG3. |
| [liveness_assumptions.lean](Resdet/liveness_assumptions.lean) | L1–L4 at request acceptance and RPC completion. |
| [safety.lean](Resdet/safety.lean) | Local invariants, Lemmas 1–2, and Theorem 1. |
| [liveness.lean](Resdet/liveness.lean) | Lemmas 3–5 and Theorem 2. |
| [dedup.lean](Resdet/dedup.lean) | First-response delivery by request ID. |

A leader issues a downstream RPC for every accepted invocation. Retries of the
same logical request can return different responses and produce distinct
proposals. Each replica processes its own learned log in index order and delivers
only the first response for each request ID.

[PROTOCOL.md](PROTOCOL.md) explains the execution model and liveness contracts.
[PAPER.md](PAPER.md) maps the numbered proofs to the paper and lists their scope.
The handler tests check retries, out-of-order callbacks, and delivery. [HandlerTests.lean](HandlerTests.lean)
The example follows one request through a leader change, retry, and delivery. [ExampleExecution.lean](ExampleExecution.lean)

Run `make check-lean` from the repository root with Lean 4.24.0 installed. To
install the pinned toolchain locally, run `make fetch-lean`. The check builds the
proofs and examples with warnings as errors, then runs [AxiomAudit.lean](AxiomAudit.lean).
The audit checks every Resdet declaration for transitive dependencies on axioms
outside Lean’s standard `propext`, `Quot.sound`, and `Classical.choice`.
