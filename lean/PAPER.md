# Correspondence with the paper

Read [resdet.lean](Resdet/resdet.lean) alongside the Section 4 pseudocode.
The blocking `send_and_recv` is split into a call and its response
continuation. The number assigned to each call lets Lean distinguish
overlapping RPCs for the same logical request. Delivery uses the request ID
alone, just as in the pseudocode.

## Numbered proofs

| Paper statement | Lean declaration |
| --- | --- |
| Lemma 1, same processed index implies same entry | `lemma_1_same_processed_entry` |
| Lemma 2, no-hole processing | `lemma_2_no_hole_processing` |
| Theorem 1, response agreement | `theorem_1_safety` and its execution form `theorem_1_on_execution` |
| Lemma 3, eventual agreement | `lemma_3_eventual_agreement` |
| Lemma 4, eventual prefix learning | `lemma_4_eventual_prefix_learning` |
| Lemma 5, eventual delivery | `lemma_5_eventual_delivery` and `lemma_5_on_execution` |
| Theorem 2, eventual delivery at every non-faulty replica | `theorem_2_liveness` |

[safety.lean](Resdet/safety.lean) proves its invariants from the handler
definitions and uses callback agreement for Theorem 1. [liveness.lean](Resdet/liveness.lean)
reuses the local invariants. Each replica can learn entries out of order, and
each numbered statement quantifies over the relevant requests and replicas.

## Scope and assumptions

- **Submissions.** The `submitted` predicate denotes logical request IDs submitted during an execution. The model abstracts over the time of the first service submission, individual transport messages, and leader election. L1 constrains acceptance of retries that stay pending. Different attempts may be accepted by different leaders.
- **Consensus.** The proofs assume the consensus interface. Section 4.1 says each callback carries the entry committed at its index. Lean states callback origin and uniqueness of the committed entry explicitly, then derives agreement between callbacks. Lemma 4 uses this property when ignoring a repeat. CG3(2) separately supplies per-request progress under repeated proposals.
- **Request identity.** The paper requires retries of one logical request to reuse its ID and body. The model carries the payload with each call and forwarding operation. It does not verify ID generation, payload consistency, or exactly-once effects at the downstream service.
- **Section 5.4.** The paper’s TLA⁺ mechanization describes an earlier model with request deduplication and a leader that remains in place. The Lean results cover the revised Section 4 pseudocode and the proofs in Sections 5.1–5.3. Neither artifact checks a translation of the other.

<a id="3-handler-atomicity-and-nonfaulty-state"></a>

### Handler atomicity and non-faulty state

One local event executes one nonblocking handler segment. RPCs may overlap
across those segments. A learn callback and its finite processing loop run as
one segment, which assumes serialized updates to local log and delivery state.
The proof covers each replica’s state within an incarnation. Restart and state
restoration, implementation locking, and refinement of the Go code are outside
its scope.
