import Resdet.Protocol

namespace Resdet.Requests

variable {Request Payload Response : Type} [DecidableEq Request]

/-- A returned response completes the accepted handler exactly once. -/
inductive Step : State Request Payload Response → State Request Payload Response → Prop
  | handle (s) (isLeader request payload) :
      Step s (handle_request isLeader request payload s)
  | resume (s) (request response) (issued : Issued s request)
      (pending : ¬ Proposed s request) :
      Step s (resume_request request response s)
  | stutter (s) : Step s s

theorem handle_request_issued (s : State Request Payload Response)
    (request : Request) (payload : Payload) :
    Issued (handle_request true request payload s) request := by
  by_cases old : request ∈ s.calls.map Prod.fst
  · simp [handle_request, Issued, old]
  · simp [handle_request, Issued, old, send_and_recv]

omit [DecidableEq Request] in
/-- The duplicate branch refers to a real earlier invocation and its body. -/
theorem issued_has_call {s : State Request Payload Response} {request : Request}
    (issued : Issued s request) : ∃ payload, (request, payload) ∈ s.calls := by
  obtain ⟨⟨rid, payload⟩, member, same⟩ := List.mem_map.mp issued
  change rid = request at same
  subst rid
  exact ⟨payload, member⟩

theorem duplicate_request_unchanged (s : State Request Payload Response)
    (request : Request) (payload : Payload) (old : Issued s request) :
    handle_request true request payload s = s := by
  simp [handle_request, show request ∈ s.calls.map Prod.fst from old]

theorem step_calls_mono {s t : State Request Payload Response} (step : Step s t) :
    s.calls ⊆ t.calls := by
  cases step with
  | handle isLeader request payload =>
      simp only [handle_request]
      split
      · exact fun _ h => h
      · split
        · exact fun _ h => h
        · exact fun _ h => List.mem_cons_of_mem _ h
  | _ => exact fun _ h => h

theorem step_issued_mono {s t : State Request Payload Response} (step : Step s t)
    {request : Request} (issued : Issued s request) : Issued t request := by
  obtain ⟨payload, member⟩ := issued_has_call issued
  exact List.mem_map_of_mem (step_calls_mono step member)

theorem step_proposals_mono {s t : State Request Payload Response} (step : Step s t) :
    s.proposals ⊆ t.proposals := by
  cases step with
  | handle isLeader request payload =>
      simp only [handle_request]
      split
      · exact fun _ h => h
      · split <;> exact fun _ h => h
  | resume => exact fun _ h => List.mem_cons_of_mem _ h
  | stutter => exact fun _ h => h

structure Invariant (s : State Request Payload Response) : Prop where
  callsUnique : (s.calls.map Prod.fst).Nodup
  proposalsUnique : (s.proposals.map Prod.fst).Nodup
  proposalFromCall : ∀ item ∈ s.proposals, Issued s item.1

omit [DecidableEq Request] in
theorem initial_invariant : Invariant ({} : State Request Payload Response) := by
  constructor <;> simp [Issued]

theorem step_preserves_invariant {s t : State Request Payload Response}
    (inv : Invariant s) (step : Step s t) : Invariant t := by
  cases step with
  | handle isLeader request payload =>
      simp only [handle_request]
      split
      · exact ⟨inv.callsUnique, inv.proposalsUnique, inv.proposalFromCall⟩
      · split
        · exact inv
        · rename_i fresh
          refine ⟨?_, inv.proposalsUnique, ?_⟩
          · simpa [send_and_recv] using And.intro fresh inv.callsUnique
          · intro item member
            exact List.mem_cons_of_mem _ (inv.proposalFromCall item member)
  | resume request response issued pending =>
      refine ⟨inv.callsUnique, ?_, ?_⟩
      · simpa [resume_request, propose, Proposed] using And.intro pending inv.proposalsUnique
      · intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact issued
        · exact inv.proposalFromCall item member
  | stutter => exact inv

end Resdet.Requests
