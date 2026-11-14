import Resdet.Liveness

/-!
A concrete infinite execution witnesses that the external contracts can hold
together: one actual invocation, one downstream response/proposal, then learning
and delivery. Later request retries are deduplicated and preserve the completed state.
-/
namespace Resdet.ContractsTests

def s0 : Replica Nat Nat Nat := {}
def s1 : Replica Nat Nat Nat :=
  { s0 with requests := Requests.handle_request true 1 42 s0.requests }
def s2 : Replica Nat Nat Nat :=
  { s1 with requests := Requests.resume_request 1 7 s1.requests }
def s3 : Replica Nat Nat Nat :=
  { s2 with delivery := handle_learn s2.delivery 1 (1, 7) }

def state : Nat → Unit → Replica Nat Nat Nat
  | 0, _ => s0
  | 1, _ => s1
  | 2, _ => s2
  | _ + 3, _ => s3

def event : Nat → Unit → Event Nat Nat Nat
  | 0, _ => .handle_request 1 42
  | 1, _ => .resume_request 1 7
  | 2, _ => .handle_learn 1 (1, 7)
  | _ + 3, _ => .handle_request 1 42

def run : Execution Unit Nat Nat Nat where
  state := state
  leader := fun _ _ => true
  event := event
  initial := fun _ => rfl
  next := by
    intro time node
    cases time with
    | zero => exact .handle_request s0 1 42
    | succ time =>
        cases time with
        | zero =>
            exact .resume_request s1 1 7 (by exact List.mem_cons_self)
              (by change ¬ (1 : Nat) ∈ ([] : List Nat); simp)
        | succ time =>
            cases time with
            | zero => exact .handle_learn s2 1 (1, 7)
            | succ time => exact .handle_request s3 1 42

theorem concrete_delivery :
    (run.state 3 ()).delivery.delivered = [(1, 7)] ∧
    (run.state 3 ()).delivery.seen = [1] ∧
    (run.state 3 ()).requests.calls = [(1, 42)] ∧
    (run.state 3 ()).requests.proposals = [(1, 7)] := by decide

def agreed (time index : Nat) (entry : Item Nat Nat) : Prop :=
  2 ≤ time ∧ index = 1 ∧ entry = (1, 7)

def nonfaulty (_ : Unit) : Prop := True
def submitted (request : Nat) : Prop := request = 1

theorem recurring_request (time : Nat) :
    run.event (time + 3) () = .handle_request 1 42 := rfl

theorem only_resume (time : Nat) (node : Unit) (request response : Nat)
    (h : run.event time node = .resume_request request response) :
    time = 1 ∧ request = 1 ∧ response = 7 := by
  cases time with
  | zero => simp [run, event] at h
  | succ time =>
      cases time with
      | zero => simpa [run, event] using h.symm
      | succ time =>
          cases time <;> simp [run, event] at h

theorem only_learn (time : Nat) (node : Unit) (index : Nat) (entry : Item Nat Nat)
    (h : run.event time node = .handle_learn index entry) :
    index = 1 ∧ entry = (1, 7) := by
  cases time with
  | zero => simp [run, event] at h
  | succ time =>
      cases time with
      | zero => simp [run, event] at h
      | succ time =>
          cases time with
          | zero => simpa [run, event] using h.symm
          | succ time => simp [run, event] at h

theorem issued_id (time : Nat) (node : Unit) (request : Nat)
    (issued : Requests.Issued (run.state time node).requests request) :
    request = 1 ∧ 1 ≤ time := by
  cases time with
  | zero => change request ∈ ([] : List Nat) at issued; simp at issued
  | succ time =>
      cases time with
      | zero => exact ⟨List.mem_singleton.mp issued, by decide⟩
      | succ time =>
          cases time with
          | zero => exact ⟨List.mem_singleton.mp issued, by decide⟩
          | succ time => exact ⟨List.mem_singleton.mp issued, by omega⟩

theorem proposed_after (time : Nat) (node : Unit) (later : 2 ≤ time) :
    Requests.Proposed (run.state time node).requests 1 := by
  cases time with
  | zero => omega
  | succ time =>
      cases time with
      | zero => omega
      | succ time =>
          cases time with
          | zero => exact List.mem_cons_self
          | succ time => exact List.mem_cons_self

theorem consensus_contract : Consensus run nonfaulty agreed := by
  constructor
  · exact ⟨0, (), trivial, rfl⟩
  · intro a b r t index left right _ _ _ hl hr
    exact (only_learn a r index left hl).2.trans (only_learn b t index right hr).2.symm
  · intro time index entry h earlier positive before
    rcases h with ⟨after, rfl, rfl⟩
    have same : earlier = 1 := by omega
    exact ⟨(1, 7), after, same, rfl⟩
  · intro time node request response _ _ occurs
    rcases only_resume time node request response occurs with ⟨rfl, rfl, rfl⟩
    exact ⟨2, 1, by decide, by decide, by decide, rfl, rfl⟩
  · intro start index entry _ h node _
    rcases h with ⟨after, rfl, rfl⟩
    cases node
    cases start with
    | zero => omega
    | succ start =>
        cases start with
        | zero => omega
        | succ start =>
            cases start with
            | zero => exact Or.inr ⟨2, Nat.le_refl _, rfl⟩
            | succ start => exact Or.inl rfl

theorem request_progress : RequestProgress run nonfaulty := by
  constructor
  intro start node request _ issued pending
  obtain ⟨rfl, positive⟩ := issued_id start node request issued
  have before : start < 2 := by
    by_cases later : 2 ≤ start
    · exact False.elim (pending (proposed_after start node later))
    · omega
  have same : start = 1 := by omega
  subst start
  exact ⟨1, 7, Nat.le_refl _, rfl⟩

theorem fault_model : FaultModel run nonfaulty := by
  constructor
  intro a b node _ _ _
  rfl

/-- Submission progress is witnessed by real retries, even after completion. -/
theorem submission_progress : SubmissionProgress run nonfaulty agreed submitted := by
  constructor
  intro start node request hs _ _ _
  change request = 1 at hs
  subst request
  cases node
  exact ⟨start + 3, 42, by omega, recurring_request start⟩

theorem safety_instance {a b : Nat} {x y : Nat}
    (hx : (1, x) ∈ (run.state a ()).delivery.delivered)
    (hy : (1, y) ∈ (run.state b ()).delivery.delivered) : x = y :=
  theorem_1_on_execution run consensus_contract.indexAgreement a b () () trivial trivial hx hy

theorem liveness_instance :
    EventuallyFrom 0 (fun time => ∃ response, (1, response) ∈
      (run.state time ()).delivery.delivered) :=
  theorem_2_liveness run fault_model consensus_contract submission_progress
    request_progress 1 rfl () trivial

end Resdet.ContractsTests
