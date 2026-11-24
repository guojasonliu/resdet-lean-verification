import Resdet

/-!
A non-faulty replica loses leadership during its first RPC. Its response 7 is
proposed but never agreed. The same replica is elected again, retries the same
request, proposes response 9, and learns that entry at index 1.
-/
namespace Resdet.ExampleExecution

def s0 : Replica Nat Nat Nat := {}
def s1 := { s0 with requests := Requests.handle_request true 1 42 s0.requests }
def s2 := { s1 with requests := Requests.resume_request 0 1 7 s1.requests }
def s3 := { s2 with requests := Requests.handle_request true 1 42 s2.requests }
def s4 := { s3 with requests := Requests.resume_request 1 1 9 s3.requests }
def s5 := { s4 with delivery := handle_learn s4.delivery 1 (1, 9) }

def state : Nat → Unit → Replica Nat Nat Nat
  | 0, _ => s0
  | 1, _ => s1
  | 2, _ => s2
  | 3, _ => s3
  | 4, _ => s4
  | _ + 5, _ => s5

def event : Nat → Unit → Event Nat Nat Nat
  | 0, _ => .handle_request 1 42
  | 1, _ => .resume_request 0 1 7
  | 2, _ => .handle_request 1 42
  | 3, _ => .resume_request 1 1 9
  | 4, _ => .handle_learn 1 (1, 9)
  | _ + 5, _ => .idle

def run : Execution Unit Nat Nat Nat where
  state := state
  leader := fun time _ => time != 1
  event := event
  initial := fun _ => rfl
  next := by
    intro time node
    match time with
    | 0 => exact .handle_request s0 1 42
    | 1 => exact .resume_request s1 0 1 7 (by decide)
    | 2 => exact .handle_request s2 1 42
    | 3 => exact .resume_request s3 1 1 9 (by decide)
    | 4 => exact .handle_learn s4 1 (1, 9)
    | _ + 5 => exact .idle s5

def nonfaulty (_ : Unit) : Prop := True
def submitted (request : Nat) : Prop := request = 1

def agreed (time index : Nat) (entry : Item Nat Nat) : Prop :=
  4 ≤ time ∧ index = 1 ∧ entry = (1, 9)

theorem concrete_delivery :
    (run.state 5 ()).requests.calls = [(1, 42), (1, 42)] ∧
    (run.state 5 ()).requests.proposals = [(1, 9), (1, 7)] ∧
    (run.state 5 ()).delivery.delivered = [(1, 9)] := by decide

theorem first_proposal_can_be_lost :
    run.leader 1 () = false ∧ run.event 1 () = .resume_request 0 1 7 ∧
    ∀ time index, ¬agreed time index (1, 7) := by simp [run, event, agreed]

theorem only_learn (time : Nat) (node : Unit) (index : Nat) (entry : Item Nat Nat)
    (h : run.event time node = .handle_learn index entry) :
    index = 1 ∧ entry = (1, 9) := by
  match time with
  | 0 | 1 | 2 | 3 | _ + 5 => simp [run, event] at h
  | 4 => simpa [run, event] using h.symm

theorem proposed_request (time : Nat) (node : Unit) (attempt request response : Nat)
    (h : run.event time node = .resume_request attempt request response) :
    request = 1 := by
  match time with
  | 0 | 2 | 4 | _ + 5 => simp [run, event] at h
  | 1 | 3 =>
    simp [run, event] at h
    exact h.2.1.symm

theorem consensus_contract : Consensus run nonfaulty agreed where
  election := ⟨0, (), trivial, rfl⟩
  agreedEntryUnique := by
    intro a b index left right _ hl hr
    exact hl.2.2.trans hr.2.2.symm
  callbackOrigin := by
    intro time node index entry _ _ occurs
    match time with
    | 0 | 1 | 2 | 3 | _ + 5 => simp [run, event] at occurs
    | 4 =>
      obtain ⟨rfl, rfl⟩ := only_learn 4 node index entry occurs
      exact ⟨4, by decide, by decide, rfl, rfl⟩
  prefixAgreement := by
    intro time index entry h earlier positive before
    rcases h with ⟨after, rfl, rfl⟩
    exact ⟨(1, 9), after, by omega, rfl⟩
  repeatedProposalProgress := by
    intro request recurring
    obtain ⟨time, n, attempt, response, _, occurs⟩ := recurring 0
    obtain rfl := proposed_request time n attempt request response occurs
    exact ⟨3, (), 1, 9, 4, 1, rfl, by decide, by decide, by decide, rfl, rfl⟩
  learnCallbacks := by
    intro start index entry _ h node _
    rcases h with ⟨after, rfl, rfl⟩
    match start with
    | 0 | 1 | 2 | 3 => omega
    | 4 => exact Or.inr ⟨4, Nat.le_refl _, rfl⟩
    | _ + 5 => exact Or.inl rfl

theorem liveness_assumptions : LivenessAssumptions run nonfaulty agreed submitted where
  requestAccepted := by
    intro cutoff request hs neverAgreed
    change request = 1 at hs
    subst request
    exact False.elim (neverAgreed ⟨4, 1, 9, by decide, by decide, rfl, rfl⟩)
  rpcCompletes := by
    intro start node attempt request _ pending
    match start with
    | 0 | 2 | 4 | _ + 5 => change _ ∈ ([] : List (Nat × Nat)) at pending; simp at pending
    | 1 =>
      have eq : (attempt, request) = (0, 1) := List.mem_singleton.mp pending
      cases eq
      exact ⟨1, 7, by decide, rfl⟩
    | 3 =>
      have eq : (attempt, request) = (1, 1) := List.mem_singleton.mp pending
      cases eq
      exact ⟨3, 9, by decide, rfl⟩

theorem safety_instance {a b : Nat} {x y : Nat}
    (hx : (1, x) ∈ (run.state a ()).delivery.delivered)
    (hy : (1, y) ∈ (run.state b ()).delivery.delivered) : x = y :=
  theorem_1_on_execution run consensus_contract.callbacksAgree a b () () trivial trivial hx hy

theorem liveness_instance :
    EventuallyFrom 0 (fun time => ∃ response, (1, response) ∈
      (run.state time ()).delivery.delivered) :=
  theorem_2_liveness run consensus_contract liveness_assumptions 1 rfl () trivial

end Resdet.ExampleExecution
