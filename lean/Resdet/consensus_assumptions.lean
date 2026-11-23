import Resdet.resdet

/-!
Sections 4.1 and 5. Consensus owns the agreed log. Each Resdet replica
records entries only when it receives a learn callback. The assumptions below
describe the interface between them.
-/
namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]

def CallbackAgreement (run : Execution Node Request Payload Response)
    (nonfaulty : Node → Prop) : Prop :=
  ∀ a b r t index left right, nonfaulty r → nonfaulty t → 1 ≤ index →
    run.event a r = .handle_learn index left →
    run.event b t = .handle_learn index right → left = right

/-- After every cutoff, some RPC continuation submits a proposal for this
request. Attempts, proposing replicas, and returned responses can differ. -/
def RepeatedProposals (run : Execution Node Request Payload Response) (request : Request) : Prop :=
  ∀ cutoff : Nat, ∃ time n attempt response, cutoff ≤ time ∧
    run.event time n = .resume_request attempt request response

structure Consensus (run : Execution Node Request Payload Response)
    (nonfaulty : Node → Prop) (agreed : Nat → Nat → Item Request Response → Prop) : Prop where
  /-- CG3(1): consensus eventually elects a non-faulty leader. -/
  election : ∃ time n, nonfaulty n ∧ run.leader time n = true
  /-- Section 4.1: a committed log index has a single entry across time. -/
  agreedEntryUnique : ∀ a b index left right, 1 ≤ index →
    agreed a index left → agreed b index right → left = right
  /-- Section 4.1: every learn callback, including a repeated callback, carries
  the entry that consensus has committed at that index. -/
  callbackOrigin : ∀ time n index entry, nonfaulty n → 1 ≤ index →
    run.event time n = .handle_learn index entry →
    ∃ atTime, atTime ≤ time ∧ agreed atTime index entry
  /-- CG2: agreement at i includes an agreed entry at every positive index through i. -/
  prefixAgreement : ∀ time index entry, agreed time index entry →
    ∀ earlier, 1 ≤ earlier → earlier ≤ index → ∃ value, agreed time earlier value
  /-- CG3(2): if proposals keep arriving for a request, some proposed entry for
  that request is agreed at a positive index. -/
  repeatedProposalProgress : ∀ request, RepeatedProposals run request →
    ∃ proposedAt n attempt response agreedAt index,
      run.event proposedAt n = .resume_request attempt request response ∧
      proposedAt ≤ agreedAt ∧ 1 ≤ index ∧ agreed agreedAt index (request, response)
  /-- CG3(3) and L4: a non-faulty replica has the agreed entry already or
  eventually runs its learn callback. -/
  learnCallbacks : ∀ start index entry, 1 ≤ index → agreed start index entry →
    ∀ n, nonfaulty n → (run.state start n).delivery.log index = some entry ∨
      EventuallyFrom start (fun time => run.event time n = .handle_learn index entry)

namespace Consensus

variable {run : Execution Node Request Payload Response} {nonfaulty : Node → Prop}
variable {agreed : Nat → Nat → Item Request Response → Prop}

/-- CG1 at the callback interface follows from the unique committed entry.
The safety proof can also use callback agreement on its own. -/
theorem indexAgreement (consensus : Consensus run nonfaulty agreed) :
    CallbackAgreement run nonfaulty := by
  intro a b r t index left right hr ht positive leftCallback rightCallback
  obtain ⟨u, _, hl⟩ := consensus.callbackOrigin a r index left hr positive leftCallback
  obtain ⟨v, _, hv⟩ := consensus.callbackOrigin b t index right ht positive rightCallback
  exact consensus.agreedEntryUnique u v index left right positive hl hv

end Consensus
end Resdet
