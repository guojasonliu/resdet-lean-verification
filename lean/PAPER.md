# Relation to the paper

The Lean model proves safety and conditional liveness for Resdet above an
abstract consensus log. It also models quorum selection, timeout fallback,
and batching. This maps the arguments in Section 5 to theorem names for human
review; it is not a checked translation of the paper.

## Claims and checked statements

Names are in `Resdet.Paper` unless qualified otherwise.

| Claim | Theorem | Qualification |
| --- | --- | --- |
| Same processed index has the same entry | `lemma_1_same_processed_entry` | Consensus agreement is represented by one shared immutable log. |
| Processing cannot skip a slot | `lemma_2_no_hole_processing` | Induction over core transitions; slots are zero-based. |
| Responses agree across replicas and times | `theorem_1_safety`; `theorem_1_crash_stop` | Compares any two deliveries of the same request ID. |
| A pending request eventually reaches agreement | `eventually_agreed` | Stable leader, ingress, pending-handler/retry fairness, and consensus progress. |
| Every finite agreed prefix is eventually learned | `eventually_prefix_learned` | Eventual learning of each slot and retention of learned state. |
| Prefix processing eventually delivers a response | `eventually_delivered` | Fair next-slot processing; suppression of duplicates leaves the first response. |
| Every submitted request reaches every non-faulty replica | `theorem_2_crash_stop` | Quorum one, crash-stop failures, and the progress assumptions below. |
| First agreed response wins, once per replica | `first_committed_response`; `Protocol.at_most_once_delivery` | Conflicting responses and duplicate log entries are allowed. |
| Batching preserves delivery | `batching_equivalent`; `rebatching_preserves_delivery` | Entry order must be preserved. |
| Applications observe the same race winner | `race_winner_for_group` | Both consume the common delivery order for the same set of request IDs. |
| Deterministic continuations agree | `deterministic_continuation` | Equal initial state, deterministic code, and equally long consumed prefixes. |

`theorem_2_crash_stop` concludes that each qualifying request/replica pair
eventually has one response in its delivery history at every later time,
with a delivery count of exactly one. This is workflow delivery, not once-only
execution of an external operation. A failed leader and its successor can both
execute that operation; `CrashStopTests.retry_can_repeat_external_execution`
checks such a reachable trace.

## Assumptions to review

- **Consensus:** a shared append-only log supplies CG1/CG2. `StableLeader` and
  `StableConsensusProgress` supply stable leadership and eventual agreement of
  that leader's actual proposal attempts. Old leaders' buffered proposals need
  not commit.
- **Ingress and handlers:** each submitted request eventually arrives;
  `PendingHandlers` requires per-request selection, dispatch, response, and
  proposal/reproposal progress while it remains unagreed. With quorum one,
  `single_arrival_ready` turns one arrival into an eligible request.
- **Learning and processing:** `DeliveryProgress` requires eventual learning
  and fair processing of the next available slot. The whole-prefix and delivery
  conclusions are proved from these premises.
- **Identity and application behavior:** equal IDs identify the same logical
  call. ID generation, request-body consistency, and application consumption of
  the delivery order are outside the model.

These contracts are theorem parameters, not additional Lean axioms. See
[PROTOCOL.md](PROTOCOL.md) for their definitions and the proof chain.

The leadership assumption also needs alignment: Lean requires a leader that
remains live and leader forever after some finite time. The current paper's
CG3(1) only says a non-faulty leader is eventually elected. This proof does not
establish liveness under indefinitely recurring leadership changes.

## Recovery remains a model gap

The current paper's Section 4 permits replicas to recover. Section 5's
mechanization discussion says recovered leaders clear volatile request
deduplication so unfinished calls can execute again. Lean's `Step.recover`
only changes availability: dispatch/execution histories, learned state, and
delivery caches remain intact. Its recovery examples check a different
abstraction.

`CrashStopBehavior` excludes recovery, and its theorems establish the
crash-stop subset. They do not settle the paper's recovery case. Extending that
result requires modeling which state survives a restart, which pending calls
are retried, and how delivery state is restored. Neither the Go correspondence
nor the TLA+ correspondence is machine-checked.
