import Resdet

/-!
A non-faulty replica loses leadership during its first RPC. It receives response
7 and later proposes it, but that proposal is lost. After reelection it handles a
retry and proposes response 9, which is agreed at index 1. Receipt of the learn
callback and completion of its handler are also separate events.
-/
namespace Resdet.ExampleExecution

def initialState : Replica Nat Nat Nat := {}
def firstCall := { initialState with requests := Requests.handle_request true 1 42 initialState.requests }
def firstReturn := { firstCall with requests := Requests.rpc_return 0 1 7 firstCall.requests }
def firstProposal := { firstReturn with requests := Requests.resume_request 0 1 7 firstReturn.requests }
def retryCall := { firstProposal with requests := Requests.handle_request true 1 42 firstProposal.requests }
def retryReturn := { retryCall with requests := Requests.rpc_return 1 1 9 retryCall.requests }
def retryProposal := { retryReturn with requests := Requests.resume_request 1 1 9 retryReturn.requests }
def learned := { retryProposal with delivery := handle_learn retryProposal.delivery 1 (1, 9) }

def state : Nat → Unit → Replica Nat Nat Nat
  | 0, _ | 1, _ => initialState
  | 2, _ => firstCall
  | 3, _ | 4, _ => firstReturn
  | 5, _ | 6, _ => firstProposal
  | 7, _ => retryCall
  | 8, _ => retryReturn
  | 9, _ | 10, _ | 11, _ => retryProposal
  | _ + 12, _ => learned

def event : Nat → Unit → Event Nat Nat Nat
  | 0, _ => .submit_request 1 42
  | 1, _ => .handle_request 1 42
  | 2, _ => .rpc_return 0 1 7
  | 3, _ => .idle
  | 4, _ => .resume_request 0 1 7
  | 5, _ => .submit_request 1 42
  | 6, _ => .handle_request 1 42
  | 7, _ => .rpc_return 1 1 9
  | 8, _ => .resume_request 1 1 9
  | 9, _ => .receive_learn 1 (1, 9)
  | 10, _ => .idle
  | 11, _ => .handle_learn 9 1 (1, 9)
  | _ + 12, _ => .idle

inductive Message
  | request (rid payload : Nat)
  | heartbeat

/-- Both requests are received at the next step. A heartbeat continues after
the requests finish, so the example also exercises repeated network sends. -/
def network : NetworkTrace Unit where
  Message := Message
  sent time _ _
    | .request rid payload => event time () = .submit_request rid payload
    | .heartbeat => True
  received time _ _
    | .request rid payload => event time () = .handle_request rid payload
    | .heartbeat => 0 < time

def run : Execution Unit Nat Nat Nat where
  state := state
  leader := fun time _ => decide (time < 2 ∨ 5 ≤ time)
  event := event
  network := network
  initial := fun _ => rfl
  next := by
    intro time node
    match time with
    | 0 => exact .submit_request initialState 1 42
    | 1 => exact .handle_request initialState 1 42
    | 2 => exact .rpc_return firstCall 0 1 7 (by decide)
    | 3 => exact .idle firstReturn
    | 4 => exact .resume_request firstReturn 0 1 7 (by decide)
    | 5 => exact .submit_request firstProposal 1 42
    | 6 => exact .handle_request firstProposal 1 42
    | 7 => exact .rpc_return retryCall 1 1 9 (by decide)
    | 8 => exact .resume_request retryReturn 1 1 9 (by decide)
    | 9 => exact .receive_learn retryProposal 1 (1, 9)
    | 10 => exact .idle retryProposal
    | 11 => exact .handle_learn retryProposal 9 1 (1, 9)
    | _ + 12 => exact .idle learned
  learnInvoked := by
    intro time node receivedAt index entry completes
    match time with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | _ + 12 => simp [event] at completes
    | 11 =>
      simp [event] at completes
      obtain ⟨rfl, rfl, rfl⟩ := completes
      exact ⟨by decide, rfl⟩

def nonfaulty (_ : Unit) : Prop := True

def agreed (time index : Nat) (entry : Item Nat Nat) : Prop :=
  9 ≤ time ∧ index = 1 ∧ entry = (1, 9)

theorem concrete_delivery :
    (run.state 12 ()).requests.calls = [(1, 42), (1, 42)] ∧
    (run.state 12 ()).requests.proposals = [(1, 9), (1, 7)] ∧
    (run.state 12 ()).delivery.delivered = [(1, 9)] := by decide

theorem return_precedes_proposal :
    run.event 2 () = .rpc_return 0 1 7 ∧
    (run.state 3 ()).requests.returned = [(0, 1, 7)] ∧
    run.event 3 () = .idle ∧ (run.state 4 ()).requests.proposals = [] ∧
    run.event 4 () = .resume_request 0 1 7 ∧
    (run.state 5 ()).requests.proposals = [(1, 7)] := by decide

theorem receipt_precedes_completion :
    run.event 9 () = .receive_learn 1 (1, 9) ∧
    (run.state 10 ()).delivery.log 1 = none ∧
    run.event 10 () = .idle ∧
    (run.state 11 ()).delivery.log 1 = none ∧
    run.event 11 () = .handle_learn 9 1 (1, 9) ∧
    (run.state 12 ()).delivery.log 1 = some (1, 9) := by decide

theorem first_proposal_can_be_lost :
    run.leader 4 () = false ∧ run.event 4 () = .resume_request 0 1 7 ∧
    ∀ time index, ¬agreed time index (1, 7) := by simp [run, event, agreed]

theorem only_receipt (time : Nat) (node : Unit) (index : Nat) (entry : Item Nat Nat)
    (h : run.event time node = .receive_learn index entry) :
    time = 9 ∧ index = 1 ∧ entry = (1, 9) := by
  match time with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 10 | 11 | _ + 12 => simp [run, event] at h
  | 9 => exact ⟨rfl, by simpa [run, event] using h.symm⟩

theorem proposed_request (time : Nat) (node : Unit) (attempt request response : Nat)
    (h : run.event time node = .resume_request attempt request response) :
    request = 1 := by
  match time with
  | 0 | 1 | 2 | 3 | 5 | 6 | 7 | 9 | 10 | 11 | _ + 12 => simp [run, event] at h
  | 4 | 8 =>
    simp [run, event] at h
    exact h.2.1.symm

theorem consensus_contract : Consensus run nonfaulty agreed where
  cg1 := by
    intro a b r t index left right _ _ _ hl hr
    cases r
    cases t
    have leftAtMax := run.log_mono () (Nat.le_max_left a b) hl
    have rightAtMax := run.log_mono () (Nat.le_max_right a b) hr
    exact Option.some.inj (leftAtMax.symm.trans rightAtMax)
  election := ⟨0, (), trivial, rfl⟩
  agreedEntryUnique := by
    intro a b index left right _ hl hr
    exact hl.2.2.trans hr.2.2.symm
  callbackOrigin := by
    intro time node index entry _ _ occurs
    obtain ⟨rfl, rfl, rfl⟩ := only_receipt time node index entry occurs
    exact ⟨9, by decide, by decide, rfl, rfl⟩
  prefixAgreement := by
    intro time index entry h earlier positive before
    rcases h with ⟨after, rfl, rfl⟩
    exact ⟨(1, 9), after, by omega, rfl⟩
  repeatedProposalProgress := by
    intro request recurring
    obtain ⟨time, n, attempt, response, _, occurs⟩ := recurring 0
    obtain rfl := proposed_request time n attempt request response occurs
    exact ⟨8, (), 1, 9, 9, 1, rfl, by decide, by decide, by decide, rfl, rfl⟩
  cg3_3 := by
    intro start index entry _ h node _
    rcases h with ⟨after, rfl, rfl⟩
    exact ⟨start, Nat.le_refl _, 9, after, rfl⟩

private theorem submission_contents {time request payload : Nat} {n : Unit}
    (sent : event time n = .submit_request request payload) : request = 1 ∧ payload = 42 := by
  match time with
  | 1 | 2 | 3 | 4 | 6 | 7 | 8 | 9 | 10 | 11 | _ + 12 => simp [event] at sent
  | 0 | 5 => simpa [event] using sent.symm

theorem liveness_assumptions : LivenessAssumptions run nonfaulty where
  l1 := by
    intro cutoff request submittedRequest stillPending
    obtain ⟨_, _, _, sent⟩ := submittedRequest
    obtain ⟨rfl, _⟩ := submission_contents sent
    exact False.elim (stillPending 12 () 9 trivial (by decide))
  l2 := by
    intro sender receiver message _ _ repeatedlySent
    cases message with
    | heartbeat => exact ⟨0, 1, trivial, Nat.zero_le 1, Nat.zero_lt_succ 0⟩
    | request rid payload =>
      obtain ⟨time, _, sent⟩ := repeatedlySent 0
      obtain ⟨rfl, rfl⟩ := submission_contents (n := ()) (time := time) sent
      exact ⟨0, 1, rfl, by decide, rfl⟩
  l3 := by
    intro acceptedAt node request payload _ _ accepted
    match acceptedAt with
    | 0 | 2 | 3 | 4 | 5 | 7 | 8 | 9 | 10 | 11 | _ + 12 => simp [run, event] at accepted
    | 1 =>
      obtain ⟨rfl, rfl⟩ : 1 = request ∧ 42 = payload := by simpa [run, event] using accepted
      exact ⟨2, 7, by decide, rfl⟩
    | 6 =>
      obtain ⟨rfl, rfl⟩ : 1 = request ∧ 42 = payload := by simpa [run, event] using accepted
      exact ⟨7, 9, by decide, rfl⟩
  l4 := by
    intro readyAt node completion _ ready
    match readyAt with
    | 0 | 1 | 3 | 4 | 5 | 6 | 8 | 10 | 11 | _ + 12 => simp [run, event, completionOf] at ready
    | 2 =>
      obtain rfl : .resume_request 0 1 7 = completion := Option.some.inj ready
      exact ⟨4, by decide, rfl⟩
    | 7 =>
      obtain rfl : .resume_request 1 1 9 = completion := Option.some.inj ready
      exact ⟨8, by decide, rfl⟩
    | 9 =>
      obtain rfl : .handle_learn 9 1 (1, 9) = completion := Option.some.inj ready
      exact ⟨11, by decide, rfl⟩

theorem safety_instance {a b : Nat} {x y : Nat}
    (hx : (1, x) ∈ (run.state a ()).delivery.delivered)
    (hy : (1, y) ∈ (run.state b ()).delivery.delivered) : x = y :=
  theorem_1_on_execution run consensus_contract.cg1 a b () () trivial trivial hx hy

theorem liveness_instance :
    EventuallyFrom 0 (fun time => ∃ response, (1, response) ∈
      (run.state time ()).delivery.delivered) :=
  theorem_2_liveness run consensus_contract liveness_assumptions 1 ⟨0, (), 42, rfl⟩ () trivial

end Resdet.ExampleExecution
