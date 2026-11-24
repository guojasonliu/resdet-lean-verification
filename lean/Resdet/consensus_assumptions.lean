import Resdet.resdet

/-!
Sections 4.1 and 5. Consensus owns the agreed log. Each Resdet replica
records entries when it runs a received learn callback. The assumptions below
describe the interface between them.
-/
namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]

/-- CG1 (index agreement). If two non-faulty replicas learn entries at the
same positive index, those entries are equal. Learning records a local log slot. -/
def CG1 (run : Execution Node Request Payload Response)
    (nonfaulty : Node → Prop) : Prop :=
  ∀ a b r t index left right, nonfaulty r → nonfaulty t → 1 ≤ index →
    (run.state a r).delivery.log index = some left →
    (run.state b t).delivery.log index = some right → left = right

/-- Receipt is visible even if the replica has yet to run the handler. -/
def ReceivedBy (run : Execution Node Request Payload Response)
    (time : Nat) (n : Node) (index : Nat) (entry : Item Request Response) : Prop :=
  ∃ receivedAt, receivedAt ≤ time ∧ run.event receivedAt n = .receive_learn index entry

/-- After every cutoff, some RPC continuation submits a proposal for this
request. Attempts, proposing replicas, and returned responses can differ. -/
def RepeatedProposals (run : Execution Node Request Payload Response) (request : Request) : Prop :=
  ∀ cutoff : Nat, ∃ time n attempt response, cutoff ≤ time ∧
    run.event time n = .resume_request attempt request response

structure Consensus (run : Execution Node Request Payload Response)
    (nonfaulty : Node → Prop) (agreed : Nat → Nat → Item Request Response → Prop) : Prop where
  /-- CG1 is an assumption of the consensus interface. -/
  cg1 : CG1 run nonfaulty
  /-- CG3(1): consensus eventually elects a non-faulty leader. -/
  election : ∃ time n, nonfaulty n ∧ run.leader time n = true
  /-- Section 4.1: a committed log index has a single entry across time. -/
  agreedEntryUnique : ∀ a b index left right, 1 ≤ index →
    agreed a index left → agreed b index right → left = right
  /-- Section 4.1: every learn callback, including a repeated callback, carries
  the entry that consensus has committed at that index. -/
  callbackOrigin : ∀ time n index entry, nonfaulty n → 1 ≤ index →
    run.event time n = .receive_learn index entry →
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
  /-- CG3(3). Every non-faulty replica eventually receives the callback for
  each agreed entry. A past receipt still counts when observing the agreed log
  again. CG2 supplies the agreed entries at all earlier indices. -/
  cg3_3 : ∀ start index entry, 1 ≤ index → agreed start index entry →
    ∀ n, nonfaulty n → EventuallyFrom start (fun time => ReceivedBy run time n index entry)

end Resdet
