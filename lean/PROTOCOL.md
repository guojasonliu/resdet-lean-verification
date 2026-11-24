# Execution and proof contracts

## A request can have several RPCs

Each replica has its own request handlers and learned log. An execution records
the state, leadership observation, and handler event for each replica at each
natural-number time. [Protocol definitions](Resdet/resdet.lean)

1. A `submit_request` event records a service submission. When a replica
   handles the request, a nonleader forwards it and a leader issues an RPC.
   Retries follow the same path.
2. The `rpc_return` event records the exact response for that numbered RPC. At
   `resume_request`, the waiting handler proposes the request ID and that
   response, even if the replica has since lost leadership.
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
| L1 | If no non-faulty replica ever delivers a response for a submitted ID, service code keeps submitting it and non-faulty leaders keep accepting it. |
| L2 | A message repeatedly sent between non-faulty components is eventually received. The execution records sends and receipts in its network trace. |
| L3 | An RPC issued by a non-faulty leader eventually returns a response for that attempt. |
| L4 | At a non-faulty replica, a request handler resumes with its returned response and proposes it. Each received learn callback also completes. |
| CG3(1) | Consensus eventually elects a non-faulty leader. L1 already supplies the leader acceptance used by Lemma 3. |
| CG3(2) | If consensus keeps receiving proposals for one ID, some proposed entry for that ID is eventually agreed at a positive index. The responses can differ. |
| CG2 | Agreement at an index implies agreement at each preceding positive index. |
| CG3(3) | Every non-faulty replica eventually receives the learn callback for each agreed entry. |

These are parameters of the theorems. An RPC continuation calls `propose` in
the same model step. This is the boundary at which consensus receives a
proposal. The model leaves routing and retries inside a consensus adapter to
its implementation. [Consensus guarantees](Resdet/consensus_assumptions.lean) · [Liveness assumptions](Resdet/liveness_assumptions.lean)

## What the proofs use

For safety, Resdet assumes CG1 directly. If two non-faulty replicas learn
entries at the same index, those entries are equal. The processing invariant
relates each replica’s delivery history to its independently learned local log.

```text
history.length = processed
history[k] = log[k + 1]       for every processed position k
seen = ids(delivered)
delivered = dedup(history)
```

For Theorem 1, compare the first indices at which the two replicas processed
the delivered request ID. If the indices match, Lemma 1 gives the same response.
If one index is earlier, Lemma 2 shows that the other replica also processed
that index. By Lemma 1 it saw the same ID there, so deduplication rules out
delivery at the later index.

For Lemma 3, suppose no entry is ever agreed for a submitted ID. A non-faulty
replica can deliver only from an agreed entry, so the request stays pending.
After any cutoff, L1 supplies another accepted invocation. By L3 its RPC
returns, and by L4 its handler proposes that response. CG3(2) then gives
agreement on one such proposal, contradicting the supposition.

For Lemma 4, CG2 gives the agreed prefix. By CG3(3), each non-faulty replica
receives the callback for each entry. By L4, each handler completes with
the agreed entry in its slot. Since learned entries persist, the whole
prefix is eventually present at that replica.

For Lemma 5, processing a complete prefix either delivers the response at the
specified index or has already delivered a response for its request ID from an
earlier index. Theorem 2 composes Lemmas 3–5.
