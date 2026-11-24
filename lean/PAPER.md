# Correspondence with the paper

Read [resdet.lean](Resdet/resdet.lean) alongside the Section 4 pseudocode.
The blocking `send_and_recv` has three observable steps. The leader issues the
RPC, the RPC returns a response (L3), and the handler resumes with that response
and proposes it (L4). A local call number distinguishes overlapping RPCs for the
same logical request. Delivery uses the request ID alone.

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
definitions and uses CG1 directly for Theorem 1. [liveness.lean](Resdet/liveness.lean)
reuses the local invariants. Each replica can learn entries out of order, and
each numbered statement quantifies over the relevant requests and replicas.

## Scope and assumptions

- **Submissions.** A `submit_request` event identifies when service code submits a request. If the request stays pending, L1 supplies repeated submissions and acceptances by non-faulty leaders. Different leaders may accept different attempts.
- **Network.** L2 states fair delivery for a message repeatedly sent between non-faulty components. Lemma 3 uses leader acceptance directly from L1, as in the paper.
- **Consensus.** CG1 assumes index agreement on the replicas’ learned entries. Section 4.1 also specifies that each callback carries the entry committed at its index. Lemma 4 uses that interface when a duplicate finds an occupied slot. CG3(3) guarantees receipt of the callback, and L4 guarantees completion of its handler.
- **Request identity.** The paper requires retries of one logical request to reuse its ID and body. The model carries the payload with each call and forwarding operation. It does not verify ID generation, payload consistency, or exactly-once effects at the downstream service.
- **Section 5.4.** The paper’s TLA⁺ mechanization describes an earlier model with request deduplication and a leader that remains in place. The Lean results cover the revised Section 4 pseudocode and the proofs in Sections 5.1–5.3. Neither artifact checks a translation of the other.

<a id="3-handler-atomicity-and-nonfaulty-state"></a>

### Handler atomicity and non-faulty state

Receipt of a learn callback and execution of its handler are separate events.
RPCs may overlap. The learn handler and its finite processing loop run as one
segment, which assumes serialized updates to local log and delivery state.
The proof covers each replica’s state within an incarnation. Restart and state
restoration, implementation locking, and refinement of the Go code are outside
its scope.
