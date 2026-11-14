# Correspondence with the paper

The definitions follow the single-entry pseudocode in the paper's Resdet design
section. The proofs follow the five lemmas and two theorems in its correctness
section. The source-to-paper correspondence is for human review; it is not a
machine-checked translation from Python or the Go implementation.

## Pseudocode

| Paper | Lean representation |
| --- | --- |
| Local `log`, `learned`, `processed` | Per-replica local entry map, high-water mark, and last processed index. Indices start at 1. |
| `handle_request` | Check leadership, forward nonleader requests, suppress accepted request IDs, otherwise issue the downstream call with its payload. |
| Blocking `send_and_recv` | Split the handler at the RPC wait; its continuation resumes with an arbitrary response. |
| `propose` | Record a consensus proposal. There is no second leadership check after the RPC. |
| `handle_learn` | Ignore a repeated index; otherwise record its local entry, update `learned`, and call `process`. |
| `process` | Drain the available contiguous local prefix and suppress duplicate delivery IDs. |
| Delivery helper | Shared `deliver` operation updates seen IDs and response history together. |

The request's `calls` history retains the body of each issued RPC and supplies
request-ID deduplication. The local `history` field records processed entries
for proofs. Neither is a hidden consensus log.

## Numbered proofs

| Paper statement | Checked statement |
| --- | --- |
| Lemma 1: same processed index implies same entry | `lemma_1_same_processed_entry`, using explicit agreement of independently learned logs. |
| Lemma 2: no-hole processing | `lemma_2_no_hole_processing`, derived from the processing-loop invariant. |
| Theorem 1: response agreement | `theorem_1_safety`; `theorem_1_on_execution` derives local invariants from the run and needs only callback agreement. |
| Lemma 3: eventual agreement | `lemma_3_eventual_agreement`, from a real accepted call, its response continuation, and consensus progress. |
| Lemma 4: eventual prefix learning | `lemma_4_eventual_prefix_learning`, from CG2 and eventual execution of learning callbacks. |
| Lemma 5: eventual delivery | `lemma_5_eventual_delivery`; `lemma_5_on_execution` applies the completed-loop result to a run. |
| Theorem 2: eventual delivery at every nonfaulty replica | `theorem_2_liveness`, composing Lemmas 3–5. |

Assumptions are theorem parameters. None is an added Lean axiom, and none
asserts eventual delivery of a request to service code.

## Assumptions that need author review

### 1. Leadership loss is a fault

`FaultModel.retainsLeadership` treats a replica that loses leadership as faulty.
Accordingly, a replica classified as nonfaulty throughout the modeled
incarnation retains leadership once elected. This is an explicit interpretation
of the paper's fault model; it is not asserted as a property of every consensus
implementation.
The paper should state the relation between leadership loss and faults so that
readers use the same meaning of nonfaulty.

`Consensus.election` (CG3(1)) supplies an eventual nonfaulty leader. Leadership
retention then implies that this leader remains leader. Stability is a consequence of the election
and fault-model contracts, rather than a separate permanent-stability premise.

`SubmissionProgress.handleRequest` represents L1/L2/L4 at completed-handler
boundaries:
a request that stays pending eventually executes a request handler at an
elected nonfaulty replica. It does not assert that the replica is still leader
at that later event. `leader_admission` derives that fact from leadership
retention.
Transport, service retries, and scheduler internals remain abstract; these
external guarantees are assumed rather than verified as implementations.

### 2. A nonfaulty response continuation remains at the leader

The request handler records an issued call only in its leader branch.
`Execution.resume_is_leader` traces each response continuation to that earlier
leader invocation. If the replica is nonfaulty, leadership retention means it
is still leader when the RPC returns and the continuation proposes. CG3(2) therefore
covers the proposal without a separate former-leader progress guarantee.

A faulty leader may lose leadership during its RPC. The pseudocode still has
no leadership recheck before proposing, but the liveness proof does not require
that faulty replica's proposal to succeed. A request that remains pending is
handled by the eventual nonfaulty leader through the submission contract.

The finite two-node demotion example in `Tests.lean` still checks the handler
behavior: both continuations can propose after demotion, and subsequent calls
with the same ID are suppressed. Under the fault model, the demoted replicas
cannot both be classified as nonfaulty. That schedule is not a counterexample
to liveness under the intended assumptions.

### 3. Handler atomicity and nonfaulty state

A local handler segment is modeled as one completed state update. The request
handler may wait at the RPC boundary; `handle_learn` and its finite processing
loop run as one segment. This assumes serialized local updates, including
atomic deduplication check-and-insert operations. The paper does not specify
the locking or scheduling implementation that supplies this behavior.

The main proof tracks persistent state within a replica incarnation. A
nonfaulty replica must preserve that state and satisfy the required progress
contracts. A failed replica that later recovers is not automatically reclassified
as nonfaulty within this same proof incarnation. Section 4 also permits recovery,
while the pseudocode contains no reset or restoration procedure. The Lean theorem does not verify restoration
of learned/delivered state, clearing volatile request deduplication, or retrying
an interrupted RPC after restart.

### 4. Identity and consensus interpretation

The paper requires equal IDs to identify the same request body. The model
retains bodies but does not verify ID generation or reject inconsistent
bodies. Body consistency is stated by the paper but is not needed for the
response-agreement algebra. Response agreement alone is not a proof that a
response answers the intended payload.

CG1 is formalized at the callback interface, across times and replicas, and
includes callbacks ignored as duplicates. The paper defines learning as
recording an entry, so this makes an additional interface interpretation
explicit: repeated callbacks for one index must carry the same entry. The
formal liveness proof also uses CG1 to show that an ignored duplicate callback
has already recorded the agreed entry. The paper's Theorem 2 lists only
CG2–CG3 and L1–L4; its premise list should include this consensus-consistency
dependency.

For an agreed entry, learning progress supplies either an already-recorded
matching entry or an eventual matching callback. This is not a proof that every
callback or delivery originated from a proposal or physical execution; those
validity properties are outside the numbered claims proved here. No consensus
algorithm, election implementation, or transport is verified.
