# Reading the Lean proof

Read the protocol definitions beside the paper's pseudocode, then the
assumptions and numbered proofs. Each replica has its own learned `log`;
consensus agreement is a premise used in the proofs, not a shared protocol
array that forces replicas to agree by construction.

| File | Purpose |
| --- | --- |
| [Protocol.lean](Resdet/Protocol.lean) | Replica state and the paper's request, learning, and processing handlers. |
| [Assumptions.lean](Resdet/Assumptions.lean) | Consensus and external progress contracts, with additions to the paper marked explicitly. |
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

The main liveness proof does not assume eventual delivery. It derives it from
actual request and callback events and explicit environment contracts. Two of
those contracts strengthen what the paper currently states; see
[PAPER.md](PAPER.md#assumptions-that-need-author-review). Recovery and concurrent
memory operations also need a separate implementation argument.

From the repository root, run `make check-lean` with Lean 4.24.0 installed, or
first run `make fetch-lean`. The command builds the proofs and examples, treats
warnings as errors, and audits every Resdet declaration. Allowed logical axioms
are `propext`, `Quot.sound`, and `Classical.choice`; no new axioms or unfinished
proofs are permitted. See [PROTOCOL.md](PROTOCOL.md) for the proof contracts.
