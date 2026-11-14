# Execution and proof contracts

## Handler execution

[Protocol.lean](Resdet/Protocol.lean) contains the request and local-delivery
handlers. [Execution.lean](Resdet/Execution.lean) connects them to executions:

| Component | Meaning |
| --- | --- |
| `Replica.requests` | Issued calls with payloads, forwarded requests, and submitted proposals. |
| `Replica.delivery` | Local learned entry map, learned/processed indices, seen delivery IDs, and response history. |
| `Execution.state` | The state of each replica at each natural-number time. |
| `Execution.leader` | The external leadership observation at each time and replica. |
| `Execution.event` | A request-handler segment, response continuation, learning callback, or idle step. |
| `Execution.next` | Each event executes the corresponding handler definition. |

`handle_request` checks leadership once. A nonleader records a forwarding
effect with the same ID and payload. A fresh leader request records an issued
RPC; an already-issued ID is suppressed. `resume_request` represents the
continuation after a response returns, and proposes without another leadership
check. Its transition requires an earlier issued call and no previous
completion for that ID at this replica.

`handle_learn` records the supplied entry in that replica's local map. It
ignores an existing index and otherwise calls `process`, which drains the
available contiguous prefix. There is no independent processing action or
additional processing-fairness premise. The processing loop updates `seen`
and `delivered` using the shared `deliver` operation.

Events complete nonblocking local segments; RPC waiting lies between request
and resume events. The model does not interleave memory operations within a
segment. Forwarding is a visible effect, but the transport implementation,
retransmission schedule, and leader election algorithm are outside the model.
Leadership may change when a replica becomes faulty. `FaultModel` requires a
replica classified as nonfaulty throughout its incarnation to retain leadership
once elected. Together with eventual election, this yields an eventual stable
nonfaulty leader; stability is derived rather than separately assumed.

## Safety

`LocalInvariant` and handler completion facts are proved from the initial
state and handler definitions. In particular:

```text
history.length = processed
history[k] = log[k + 1] for each processed position k
seen = ids(delivered)
delivered = dedup(history)
```

`history` is proof instrumentation. The handlers never consult it when
checking a guard or selecting a response.

`IndexAgreement` states CG1 for two independently learned local logs and may
compare different times. Lemma 1 combines CG1 with the processing invariant.
Lemma 2 establishes the complete processed prefix. Theorem 1 compares the two
prefixes and uses request-ID deduplication to establish equal responses. Local
at-most-once delivery follows from the same invariant without a progress
assumption. `theorem_1_on_execution` derives local invariants from the run
and requires only `CallbackAgreement`, without any liveness premises.

## Environment and liveness

[Assumptions.lean](Resdet/Assumptions.lean) describes an external agreed-entry
relation, nonfaulty replicas, and the following contracts. They are theorem
parameters rather than added Lean axioms.

| Contract | What it supplies |
| --- | --- |
| `FaultModel.retainsLeadership` | A nonfaulty replica that is leader remains leader at later times; losing leadership means becoming faulty. |
| `Consensus.election` (CG3(1)) | Some nonfaulty replica is eventually elected leader. |
| `Consensus.indexAgreement` (CG1 interpretation) | Cross-time agreement of callback entries at the same positive index, including duplicate callbacks the handler ignores. |
| `Consensus.prefixAgreement` (CG2) | An agreed index has an agreed entry at every earlier positive index. |
| `Consensus.currentLeaderProgress` (CG3(2)) | A response continuation that proposes at a nonfaulty current leader eventually has its entry agreed. |
| `Consensus.learnCallbacks` (CG3(3) + L4) | An agreed entry is already recorded or eventually has a matching concrete `handle_learn` event at each nonfaulty replica. The event executes the callback, including prefix processing. |
| `RequestProgress.resume` (L3 + L4) | An issued, incomplete call at a nonfaulty replica eventually has a concrete `resume_request` event. That event executes the continuation and emits a proposal. |
| `SubmissionProgress.handleRequest` (L1/L2/L4) | A submitted request that stays pending eventually executes a request handler at a nonfaulty replica observed as leader at the starting time. It does not assert leadership at the later handler event. |

`leader_admission` derives leader handling from `Consensus.election`,
`SubmissionProgress.handleRequest`, and leadership retention. The submission
contract combines L1/L2/L4 at the execution model's handler boundary; transport,
service retries, and scheduler internals are not independently implemented.

`Execution.resume_is_leader` traces a response continuation back to the actual
leader invocation that issued its RPC. Leadership retention makes the
nonfaulty replica still leader at the continuation, so ordinary CG3(2) supplies
proposal progress. There is no extra consensus guarantee for demoted replicas.
A proposal from a faulty leader may be abandoned; pending requests still reach
the eventual nonfaulty leader through submission progress.

Combined L3/L4 and callback/L4 contracts refer to actual handler events, not
assumed eventual proposal or delivery histories. Learning progress allows an
entry already recorded, so it does not demand an infinite stream of duplicate
callbacks for an old agreement.

The liveness chain is:

```text
Lemma 3: election + submission + leadership retention
         -> leader handling -> issued call -> leader continuation -> agreement
Lemma 4: agreed index -> agreed finite prefix -> executed learning callbacks
Lemma 5: learned prefix -> completed processing loop -> delivered response
Theorem 2: compose Lemmas 3, 4, and 5
```

A callback may find the requested ID already delivered from an earlier index;
Lemma 5 therefore promises a response for the ID, not necessarily the response
at the particular agreed index used in its premise. Theorem 1 supplies response
agreement. The formal liveness proof also uses CG1 when a repeated callback
finds an existing local entry: the old entry must equal the agreed callback
value. The paper's Theorem 2 premise list currently omits this dependency.
Delivery history grows, so an established delivery is not retracted.

See [PAPER.md](PAPER.md#assumptions-that-need-author-review) for the leadership/fault
interpretation, recovery limits, body-identity contract, and serialized-handler
assumption. The checks prove the definitions and conditional statements in this
repository; they do not establish those external contracts in an implementation.
[ContractsTests.lean](ContractsTests.lean) supplies a complete execution satisfying
the contracts, while [Tests.lean](Tests.lean) checks the handler examples and the
finite demotion scenario, whose demoted replicas cannot all be nonfaulty under
this fault model.
