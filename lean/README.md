# Reading the Lean proof

Read the protocol definitions beside the paper's pseudocode, then the
assumptions and numbered proofs. Each replica has its own learned `log`;
consensus agreement is a premise used in the proofs, not a shared protocol
array that forces replicas to agree by construction.

| File | Purpose |
| --- | --- |
| [Protocol.lean](Resdet/Protocol.lean) | Replica state and the paper's request, learning, and processing handlers. |
| [Assumptions.lean](Resdet/Assumptions.lean) | Consensus, fault-model, and external progress contracts with their paper correspondence. |
| [Safety.lean](Resdet/Safety.lean) | Lemmas 1–2 and Theorem 1: equal processed entries, no holes, and response agreement. |
| [Liveness.lean](Resdet/Liveness.lean) | Lemmas 3–5 and Theorem 2: agreement, prefix learning, and delivery. |
| [RequestProofs.lean](Resdet/RequestProofs.lean) | Request deduplication, legal response continuations, and proposal origins. |
| [HandlerProofs.lean](Resdet/HandlerProofs.lean) | Induction over the actual processing loop and local callback invariants. |
| [Execution.lean](Resdet/Execution.lean) | Runs of handler events and facts that persist along those runs. |
| [Dedup.lean](Resdet/Dedup.lean), [Delivery.lean](Resdet/Delivery.lean) | One first-ID-wins scan and one stateful delivery operation. |
| [Tests.lean](Tests.lean) | Checked examples of reordered callbacks, duplicates, forwarding, and demotion during an RPC. |
| [ContractsTests.lean](ContractsTests.lean) | A complete execution satisfying the liveness contracts and instantiating the theorems. |
| [Audit.lean](Audit.lean) | Transitive axiom audit of all declarations in the Resdet namespace. |

`history` is proof instrumentation recording entries that `process` handled.
It never controls a branch or chooses a response. The key invariant, proved
from the code, is:

```text
history.length = processed
history[k] = log[k + 1]       for every processed position k
seen = ids(delivered)
delivered = dedup(history)
```

The processing loop uses `learned - processed` as a termination bound. That is
the distance to the current highest learned index, not a fixed model-checking
bound. It stops at the first missing local entry, exactly as the paper does.

The main liveness proof derives delivery from actual request and callback
events. A nonfaulty leader retains leadership under the fault model; CG3's
eventual election and request submission progress then yield an executing
leader handler. The same retention rule keeps a nonfaulty RPC continuation at
the leader, so CG3(2) applies to its proposal. These are derived facts, not
separate admission or former-leader proposal-progress assumptions.

The paper should state the leadership/fault interpretation explicitly. See
[PAPER.md](PAPER.md#assumptions-that-need-author-review) for that interpretation,
the callback-consistency dependency, and the recovery and concurrency limits.

From the repository root, run `make check-lean` with Lean 4.24.0 installed, or
first run `make fetch-lean`. The command builds the proofs and examples, treats
warnings as errors, and audits every Resdet declaration. Allowed logical axioms
are `propext`, `Quot.sound`, and `Classical.choice`; no new axioms or unfinished
proofs are permitted. See [PROTOCOL.md](PROTOCOL.md) for the proof contracts.
