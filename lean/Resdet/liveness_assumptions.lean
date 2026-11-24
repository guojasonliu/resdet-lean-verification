import Resdet.consensus_assumptions

/-! Section 5, L1–L4. Service retries, transport, RPCs, and local scheduling
are external to Resdet. These assumptions describe their observable effects
at the request handler. Callback progress is in `Consensus.learnCallbacks`. -/
namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]

/-- Section 5 progress assumptions for the request handler. -/
structure LivenessAssumptions (run : Execution Node Request Payload Response)
    (nonfaulty : Node → Prop) (agreed : Nat → Nat → Item Request Response → Prop)
    (submitted : Request → Prop) : Prop where
  /-- L1 at the receiving end of the network (L2). If no entry for a submitted
  request is ever agreed, then after every cutoff another invocation passes
  the leader check at a non-faulty replica. -/
  requestAccepted : ∀ cutoff request, submitted request →
    (¬ ∃ time index response, 1 ≤ index ∧ agreed time index (request, response)) →
    ∃ time n payload, cutoff ≤ time ∧ nonfaulty n ∧ run.leader time n = true ∧
      run.event time n = .handle_request request payload
  /-- L3 and L4. Each outstanding RPC issued by a non-faulty replica in the
  leader branch returns and its own handler resumes, even across a leader change. -/
  rpcCompletes : ∀ start n attempt request, nonfaulty n →
    (attempt, request) ∈ (run.state start n).requests.pending →
    ∃ time response, start ≤ time ∧ run.event time n = .resume_request attempt request response

end Resdet
