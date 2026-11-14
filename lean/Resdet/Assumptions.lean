import Resdet.Execution
import Resdet.Safety

/-!
Consensus and environment contracts, passed as theorem premises rather than
Lean axioms. Agreement is an external relation; there is no shared log from
which replicas read entries. The fault model treats leadership loss as a
failure, so replicas designated non-faulty retain leadership once elected.
-/
namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]

def CallbackAgreement (run : Execution Node Request Payload Response)
    (nonfaulty : Node → Prop) : Prop :=
  ∀ a b r t index left right, nonfaulty r → nonfaulty t → 1 ≤ index →
    run.event a r = .handle_learn index left →
    run.event b t = .handle_learn index right → left = right

/-- Leadership is lost only through a fault. `nonfaulty` identifies replicas
that remain non-faulty throughout this execution/incarnation. -/
structure FaultModel (run : Execution Node Request Payload Response)
    (nonfaulty : Node → Prop) : Prop where
  retainsLeadership : ∀ a b n, nonfaulty n → a ≤ b →
    run.leader a n = true → run.leader b n = true

structure Consensus (run : Execution Node Request Payload Response)
    (nonfaulty : Node → Prop) (agreed : Nat → Nat → Item Request Response → Prop) : Prop where
  /-- CG3(1): consensus eventually elects a non-faulty leader. -/
  election : ∃ time n, nonfaulty n ∧ run.leader time n = true
  /-- CG1 at the callback interface, including repeat callbacks and different times. -/
  indexAgreement : CallbackAgreement run nonfaulty
  /-- CG2: agreement at i includes an agreed entry at every positive index through i. -/
  prefixAgreement : ∀ time index entry, agreed time index entry →
    ∀ earlier, 1 ≤ earlier → earlier ≤ index → ∃ value, agreed time earlier value
  /-- CG3(2): an actual proposal by a current non-faulty leader eventually agrees. -/
  currentLeaderProgress : ∀ time n request response, nonfaulty n → run.leader time n = true →
    run.event time n = .resume_request request response →
    ∃ later index, time ≤ later ∧ 1 ≤ index ∧ agreed later index (request, response)
  /-- CG3(3) plus L4: the learn callback is received and its handler completes. -/
  learnCallbacks : ∀ start index entry, 1 ≤ index → agreed start index entry →
    ∀ n, nonfaulty n → (run.state start n).delivery.log index = some entry ∨
      EventuallyFrom start (fun time => run.event time n = .handle_learn index entry)

/-- L3 plus L4: a pending issued RPC returns and its handler continuation runs.
The conclusion is a concrete event, not eventual proposal, agreement, or delivery. -/
structure RequestProgress (run : Execution Node Request Payload Response)
    (nonfaulty : Node → Prop) : Prop where
  resume : ∀ start n request, nonfaulty n → Requests.Issued (run.state start n).requests request →
    ¬ Requests.Proposed (run.state start n).requests request →
    ∃ time response, start ≤ time ∧ run.event time n = .resume_request request response

/-- L1/L2 plus L4 at the completed-handler boundary: a pending request is
received and its handler runs at a non-faulty node observed as leader at `start`.
This field does not assert leadership when the handler executes; the fault model
supplies that fact. Transport retries and scheduling are external contracts. -/
structure SubmissionProgress (run : Execution Node Request Payload Response)
    (nonfaulty : Node → Prop) (agreed : Nat → Nat → Item Request Response → Prop)
    (submitted : Request → Prop) : Prop where
  handleRequest : ∀ start n request, submitted request → nonfaulty n →
    run.leader start n = true →
    (¬ ∃ time index response, 1 ≤ index ∧ agreed time index (request, response)) →
    ∃ time payload, start ≤ time ∧ run.event time n = .handle_request request payload

namespace Execution

variable (run : Execution Node Request Payload Response)
variable {nonfaulty : Node → Prop} {agreed : Nat → Nat → Item Request Response → Prop}

/-- A non-faulty response continuation still belongs to the current leader.
Its call originated in a leader handler; leadership retention bridges the RPC wait. -/
theorem resume_is_leader (faults : FaultModel run nonfaulty)
    (time : Nat) (n : Node) (request : Request) (response : Response)
    (hn : nonfaulty n) (event : run.event time n = .resume_request request response) :
    run.leader time n = true := by
  have step := run.next time n
  rw [event] at step
  obtain ⟨earlier, _, before, leader, _⟩ := run.issued_origin time n step.resume_issued
  exact faults.retainsLeadership earlier time n hn (Nat.le_of_lt before) leader

/-- Recorded local entries originated at callbacks, so CG1 applies to them. -/
theorem index_agreement (cg1 : CallbackAgreement run nonfaulty)
    (a b : Nat) (r t : Node) (hr : nonfaulty r) (ht : nonfaulty t) :
    IndexAgreement (run.state a r).delivery (run.state b t).delivery := by
  intro index left right positive hl hr'
  obtain ⟨u, _, callbackL⟩ := run.log_origin a r hl
  obtain ⟨v, _, callbackR⟩ := run.log_origin b t hr'
  exact cg1 u v r t index left right hr ht positive callbackL callbackR

/-- A repeated callback is safe to ignore because CG1 also covers its old value. -/
theorem learn_event_recorded (cg1 : CallbackAgreement run nonfaulty)
    (time : Nat) (n : Node) (hn : nonfaulty n) (index : Nat) (entry : Item Request Response)
    (positive : 1 ≤ index) (event : run.event time n = .handle_learn index entry) :
    (run.state (time + 1) n).delivery.log index = some entry := by
  have step := run.next time n
  rw [event] at step
  rw [step.learn_result]
  cases recorded : (run.state time n).delivery.log index with
  | none => exact handle_learn_records _ _ _ recorded
  | some old =>
      obtain ⟨earlier, _, callback⟩ := run.log_origin time n recorded
      have same := cg1 earlier time n n index old entry hn hn positive callback event
      simp [handle_learn, recorded, same]

end Execution

/-- Theorem 1 on actual executions; local invariants are proved from the handlers. -/
theorem theorem_1_on_execution (run : Execution Node Request Payload Response)
    {nonfaulty : Node → Prop}
    (cg1 : CallbackAgreement run nonfaulty) (a b : Nat) (r t : Node)
    (hr : nonfaulty r) (ht : nonfaulty t) {request : Request} {left right : Response}
    (hl : (request, left) ∈ (run.state a r).delivery.delivered)
    (hr' : (request, right) ∈ (run.state b t).delivery.delivered) : left = right :=
  theorem_1_safety (run.invariant a r) (run.invariant b t)
    (run.index_agreement cg1 a b r t hr ht) hl hr'

end Resdet
