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

### 1. A request needs an executing leader handler

CG3(1) says that a nonfaulty leader is eventually elected. L1–L2 concern request
and message receipt; L4 concerns eventual execution. Those statements do not
alone ensure that a pending request's handler runs while its recipient is
still leader. Every arrival or scheduled handler could finish after a change
of leadership.

The formal liveness theorem explicitly requires a pending request to reach an
executing handler at a nonfaulty current leader. This combines routing,
retries, and scheduling into a stronger admission contract. It is not claimed
to follow from CG3(1) and L1–L2 as currently written. Those election and transport
properties are not independently formalized in this development. In particular, L2 promises
delivery only when a message is repeatedly sent; it does not provide those
repeated sends. The paper's service retry policy is prose outside the handler.

### 2. A response may return after its leader is demoted

The pseudocode checks leadership only before `send_and_recv`. Its continuation
still proposes if leadership changes during the RPC. Printed CG3(2) guarantees
agreement for entries proposed by a nonfaulty **leader**, which may exclude
that continuation's proposal.

The formal liveness theorem separately requires consensus progress for these
former-leader proposals. This strengthens the printed consensus contract; it
is not an implementation of proposal retry or forwarding inside consensus.
An alternative would be a protocol change that preserves and retries such
proposals, or an explicit execution restriction ensuring leadership at the
proposal. The Lean handlers do not silently add either behavior. No permanent
stable-leader assumption is used.

A concrete problematic execution is:

1. A accepts a request as leader and starts its RPC.
2. B becomes leader; A returns and proposes as a follower.
3. B accepts the same request and starts its RPC.
4. A becomes leader; B returns and proposes as a follower.
5. Both replicas suppress future requests with that ID as duplicates.

If consensus is permitted to ignore both follower proposals, there need never
be an agreed response, even if A now remains leader forever. The finite
handler prefix and the suppressed subsequent retries are kernel-checked in
`Tests.both_proposals_after_demotion` and
`Tests.later_leader_retries_suppressed`. Those finite examples do not claim to
check all infinite liveness contracts.

### 3. Handler atomicity and nonfaulty state

A local handler segment is modeled as one completed state update. The request
handler may wait at the RPC boundary; `handle_learn` and its finite processing
loop run as one segment. This assumes serialized local updates, including
atomic deduplication check-and-insert operations. The paper does not specify
the locking or scheduling implementation that supplies this behavior.

The main proof tracks persistent state within a replica incarnation. A
nonfaulty replica must preserve that state and satisfy the required progress
contracts. Section 4 also permits recovery, while the pseudocode contains no
reset or restoration procedure. The Lean theorem does not verify restoration
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
formal liveness proof also uses CG1 to show that an ignored duplicate callback has already recorded the
agreed entry. The paper's Theorem 2 lists only CG2–CG3 and L1–L4; its premise
list should include this consensus-consistency dependency.

For an agreed entry, learning progress supplies either an already-recorded
matching entry or an eventual matching callback. This is not a proof that every
callback or delivery originated from a proposal or physical execution; those
validity properties are outside the numbered claims proved here. No consensus
algorithm, election implementation, or transport is verified.
