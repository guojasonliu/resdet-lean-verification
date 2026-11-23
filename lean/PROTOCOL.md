# Execution and proof contracts

## A request can have several RPCs

Each replica has its own request handlers and learned log. An execution records
the state, leadership observation, and handler event for each replica at each
natural-number time. [Protocol definitions](Resdet/resdet.lean)

1. A nonleader forwards the request ID and payload. A leader accepts the
   invocation and issues an RPC, including when it has seen that ID before.
2. The RPC can return after leadership changes. Its continuation proposes the
   pair of request ID and response to consensus. Each physical invocation gets
   a local number so the model can match an RPC return to its waiting handler.
   This number is never proposed or used to suppress a retry.
3. A learn callback records its entry at the supplied index if the index is new.
   The handler then processes the contiguous prefix available from the next
   unprocessed index. A repeated callback for an existing index returns
   immediately. During processing, only the first entry for a given request ID
   delivers a response to service code.

A missing index stops the loop until a later callback fills the gap.
`learned - processed` bounds each invocation of the loop. The bound grows
with the actual log. `history` records processed entries for the proofs.

## Progress assumptions

| Paper | Lean contract |
| --- | --- |
| L1 and L2 | If a submitted logical request never gets an agreed entry, then after every cutoff some non-faulty replica accepts an invocation as leader. Transport and service retries are represented at this acceptance boundary. |
| L3 and L4 | Each particular outstanding RPC at a non-faulty replica eventually returns and executes its continuation. The replica can change roles during the wait. |
| CG3(1) | Consensus eventually elects a non-faulty leader. L1 already supplies the leader acceptance used by Lemma 3. |
| CG3(2) | If consensus keeps receiving proposals for one ID, some proposed entry for that ID is eventually agreed at a positive index. The responses can differ. |
| CG2 | Agreement at an index implies agreement at each preceding positive index. |
| CG3(3) and L4 | Each non-faulty replica either already has the agreed entry or eventually executes its matching learn callback. |

These are parameters of the theorems. An RPC continuation calls `propose` in
the same model step. This is the boundary at which consensus receives a
proposal. The model leaves routing and retries inside a consensus adapter to
its implementation. [Consensus guarantees](Resdet/consensus_assumptions.lean) · [Liveness assumptions](Resdet/liveness_assumptions.lean)

## What the proofs use

For safety, the processing invariant relates each replica’s delivery history
to its independently learned local log.

```text
history.length = processed
history[k] = log[k + 1]       for every processed position k
seen = ids(delivered)
delivered = dedup(history)
```

For Lemma 3, suppose no entry is ever agreed for a submitted request. After
any cutoff, L1 supplies a new accepted invocation, and L3/L4 supply its
continuation. Thus consensus receives proposals for that ID after every cutoff.
CG3(2) gives agreement on some proposed entry, contradicting the supposition.

For Lemma 4, a positive index has one committed value across time and each
learn callback at a non-faulty replica carries that value. Together these
Section 4.1 assumptions imply agreement between callbacks, even duplicates at
the same replica. Once a callback completes, the local slot contains the
agreed value, whether it was just written or was already present. CG2 and
CG3(3) extend this argument to the finite prefix.

For Lemma 5, processing a complete prefix either delivers the response at the
specified index or has already delivered a response for its request ID from an
earlier index. Theorem 2 composes Lemmas 3–5.
