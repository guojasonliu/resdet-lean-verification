# Resdet in Lean

This project proves response agreement, duplicate suppression, and conditional
delivery liveness for an abstract Resdet model. Consensus supplies a shared,
append-only log; its implementation is not verified here. The proofs have no
fixed bound on replicas, requests, batches, or execution length.

**Scope:** the main failure-model interface is crash-stop: failed replicas stay
down. The current paper also permits recovery. The optional `recover` action
retains all protocol state, so it does not model a process restart that clears
volatile request-deduplication state. These results do not establish recovery
correctness of the current paper or implementation. See [PAPER.md](PAPER.md).

## Check the proofs

From the repository root:

```sh
make fetch-lean    # one-time local installation, if needed
make check-lean    # build, regression examples, and axiom audit
```

The project uses **Lean 4.24.0** and its bundled standard library, with no
external Lean packages. To use an existing toolchain:

```sh
LEAN_BIN=/absolute/path/to/lean-4.24.0/bin make check-lean
```

`lake build` alone omits the axiom audit. `make check-lean` treats warnings as
errors and checks the transitive axioms of every `Resdet` declaration, including
tests. Only `propext`, `Quot.sound`, and `Classical.choice` are allowed; unfinished
proofs, user axioms, and native-evaluation axioms fail the check.

## Reading order

Start with the definitions and theorem statements, then read their proofs.

| File | What to review |
| --- | --- |
| [Dedup.lean](Resdet/Dedup.lean) | Shared first-occurrence scan and its uniqueness, coverage, and batch-composition guarantees. |
| [Delivery.lean](Resdet/Delivery.lean) | Thin delivery wrappers around the shared helper, using either IDs from the delivery history or separately stored delivered IDs. |
| [Model.lean](Resdet/Model.lean) | Four core actions: append, learn, process, stutter. The invariant connects each stored delivery history to a deduplicated log prefix. |
| [Safety.lean](Resdet/Safety.lean) | Agreement and at-most-once delivery follow from that invariant. |
| [Protocol.lean](Resdet/Protocol.lean), [ProtocolSafety.lean](Resdet/ProtocolSafety.lean) | Request arrival, dispatch, responses, retries, and failures; a proved projection to the core and response provenance. |
| [Temporal.lean](Resdet/Temporal.lean), [ProtocolLiveness.lean](Resdet/ProtocolLiveness.lean), [ProposalRetry.lean](Resdet/ProposalRetry.lean) | Handler progress, stable-leader proposal attempts, and prefix processing yield delivery. |
| [Paper.lean](Resdet/Paper.lean), [CrashStop.lean](Resdet/CrashStop.lean) | Agreement across different times and eventual permanent delivery to non-faulty replicas. |

The key invariant is:

```text
replica.delivered = dedup(flatten(log.take(replica.processed)))
```

It is proved by induction over transitions, not assumed by the process rule.
The log may contain conflicting responses for the same request ID. Processing
in log order and keeping the first occurrence makes replicas agree.

`dedupFrom seen items` is the single duplicate-suppression implementation.
It returns the first item for each ID absent from `seen`. The delivery wrappers
append those items to the history; the protocol wrapper also updates its
delivered-ID state. Their consistency proof connects the explicit state to the
history without introducing another deduplication algorithm.

Liveness uses explicit assumptions about ingress, a stable live leader,
handler/downstream progress, consensus, and learning. None directly asserts
eventual workflow delivery. Their meanings and the supplementary stronger
progress interface are in [PROTOCOL.md](PROTOCOL.md).

## Regression examples and limits

- [Tests.lean](Tests.lean): reordered learning, conflicting responses, batches,
  and examples showing why deduplication and prefix processing matter.
- [ProtocolTests.lean](ProtocolTests.lean): request arrival, authorized dispatch, failover,
  repeated physical execution, retained-state recovery, retries, and a stalled
  execution showing why liveness needs fairness.
- [CrashStopTests.lean](CrashStopTests.lean): a failed leader stays down while
  its successor retries and the survivors deliver.
- [PaperTests.lean](PaperTests.lean): batching and application-order examples.

These examples supplement the general proofs. They do not establish that the
model matches the implementation. There is no checked refinement from Go or
TLA+, no verification of request-ID generation, and no guarantee of exactly-once
external side effects. Application-order results assume that the application
consumes Resdet's delivery order.
