# Model and proof contracts

## State and transitions

`Protocol.State` contains a delivery core and protocol histories:

| Field | Meaning |
| --- | --- |
| `core.log` | Shared append-only log of response batches. |
| `core.replica` | Per-replica learned slots, processed prefix length, and delivered responses. |
| `seen` | Request IDs whose responses have already been delivered. |
| `leader`, `up` | Current leader and replica availability. |
| `requests` | Global history of nested invocations `(rid, payload)` made available to Resdet. |
| `dispatches`, `executions` | Sender/request/leader snapshots and sender/request/response histories. |
| `observed`, `proposed` | Returned responses and proposed response entries. |

`Step` allows request arrival, leader-only dispatch, response, proposal or
reproposal, consensus append, learning, processing, crash, recovery, election,
and stuttering. A received request can be dispatched by the live leader if
that leader has not dispatched its ID before. With crashes disabled, a fixed
leader and this local freshness check imply globally unique dispatch.

`receive` is an environment action recording an invocation, not execution of
a particular replica's handler. It has no node or availability guard; arrivals
can be recorded while replicas are down. The history survives leader changes,
so forwarding and delivery of retries to a particular new leader are abstracted
away. Repeated arrivals with the same ID are allowed.

Request bodies are recorded at arrival but are not carried through downstream
execution. Responses may be arbitrary. Crash/recovery retains all histories
and delivery-deduplication state; it is not a volatile-state restart model.
See the [paper correspondence](PAPER.md#recovery-remains-a-model-gap).

## Safety proof

1. Both delivery handlers use `dedupFrom` in `Dedup.lean`. Its guarantees cover
   unique fresh IDs, provenance, coverage, and composition across batches.
   `applyWithDedup_correct` relates explicit delivered-ID state to the core handler.
2. `reachable_dedup_consistent` proves `seen` always equals the delivered request IDs.
3. `step_refines` and `reachable_refines` project protocol executions to core
   executions, allowing core stuttering for protocol-only actions.
4. The core invariant proves each delivered sequence is the deduplicated
   processed log prefix. This yields agreement, prefix agreement, and
   at-most-once delivery.
5. `Protocol.all_safety` combines those results with request, dispatch, and
   response provenance: delivered items have a received invocation, a physical
   execution, a proposal, and an agreed log entry.

Safety holds for arbitrary finite reachable executions, including reordered
learning, conflicting responses, and repeated agreement of the same ID. It
needs no fairness. Unique physical dispatch requires crashes to be disabled;
workflow delivery remains at most once even with failures.

## Liveness proof

A `Behavior` starts at the initial state and takes a `Step` at every natural
time. `WeakFair enabled occurs` means an action that remains enabled from any
time onward eventually occurs. The principal interface is
`Paper.PendingHandlers` plus `Protocol.StableConsensusProgress`:

| Assumption | Required progress |
| --- | --- |
| `StableLeader` | After a finite time, one node stays live and remains leader. |
| Ingress / `Received` | Each submitted request eventually appears in the global received-request history. |
| `PendingHandlers` | Per-request weak fairness of dispatch, response, and proposal attempts while the request is unagreed. Response progress includes the downstream-service contract. |
| `StableConsensusProgress` | Actual proposal attempts by the stable leader eventually appear in the log. |
| `DeliveryProgress` | Each agreed slot is eventually learned, and enabled next-slot processing is weakly fair. |

The proof chain is:

```text
eventually_executed                received request -> dispatch -> response
eventually_agreed_stable_consensus retry attempt -> consensus agreement
eventually_processed              induction over a finite log prefix
agreed_eventually_delivered       processed prefix -> a response for the ID
Paper.theorem_2_liveness          ingress + stabilization -> permanent delivery
Paper.theorem_2_crash_stop        specialize to non-faulty crash-stop replicas
```

`Paper.eventually_agreed` only requires handler fairness while the request is
pending: either it is already agreed, or those pending-handler premises yield
the stage progress above. No premise directly assumes eventual workflow
delivery. Per-request fairness is stronger than aggregate-action fairness that
could indefinitely starve one request among infinitely many.

`Step.repropose` represents an actual attempt even when the response is already
buffered. Consensus progress applies to the stable leader's attempts, not
automatically to an old leader's uncommitted buffer contents.
`retry_enabled_has_step` checks that an enabled attempt has a transition.

The supplementary `LocalProgress` / `ConsensusProgress` interface and
`eventual_delivery` theorem require every buffered proposal to reach agreement.
That stronger contract is not used by the main paper-facing theorem.
`RetryProgress` is an intermediate form with handler fairness even after
agreement; `PendingHandlers` avoids that unnecessary requirement.

## TLA+ correspondence and tests

The correspondence is manual. `DecideOne`/`DecidePair`, `LearnSlot`, and
`ProcessContiguous` correspond to core append, learn, and process actions.
Lean uses zero-based slots and arbitrary finite batches (including empty ones),
with singleton batches representing basic Resdet entries. It has
no `MaxSlots` bound, and no unique-first scheduling restriction. It permits
repeated learning and explicit reproposal attempts. These differences are
not covered by a machine-checked translation.

Regression traces exercise single and repeated request arrivals, rejection of
dispatch before receipt, reordered learning, duplicate/conflicting responses,
failover, and repeated physical execution.
`fairness_is_necessary` exhibits a legal execution that learns an entry and
then stalls forever. Contract-satisfiability witnesses check that the liveness
premises can hold together; they do not establish runtime fairness. Run
`make check-lean` for all proofs, examples, and the transitive axiom audit.
