import Resdet.RequestProofs
import Resdet.HandlerProofs

namespace Resdet

structure Replica (Request Payload Response : Type) where
  requests : Requests.State Request Payload Response := {}
  delivery : LocalState Request Response := initialLocal

inductive Event (Request Payload Response : Type)
  | handle_request (request : Request) (payload : Payload)
  | resume_request (request : Request) (response : Response)
  | handle_learn (index : Nat) (entry : Item Request Response)
  | idle
  deriving DecidableEq

variable {Node Request Payload Response : Type} [DecidableEq Request]

/-- Each event completes one nonblocking handler segment. RPC waiting occurs
between `handle_request` and `resume_request`; the latter does not query leadership. -/
inductive Step (isLeader : Bool) : Event Request Payload Response →
    Replica Request Payload Response → Replica Request Payload Response → Prop
  | handle_request (s) (request payload) :
      Step isLeader (.handle_request request payload) s
        { s with requests := Requests.handle_request isLeader request payload s.requests }
  | resume_request (s) (request response)
      (issued : Requests.Issued s.requests request)
      (pending : ¬ Requests.Proposed s.requests request) :
      Step isLeader (.resume_request request response) s
        { s with requests := Requests.resume_request request response s.requests }
  | handle_learn (s) (index entry) :
      Step isLeader (.handle_learn index entry) s
        { s with delivery := handle_learn s.delivery index entry }
  | idle (s) : Step isLeader .idle s s

structure Execution (Node Request Payload Response : Type) [DecidableEq Request] where
  state : Nat → Node → Replica Request Payload Response
  leader : Nat → Node → Bool
  event : Nat → Node → Event Request Payload Response
  initial : ∀ n, state 0 n = {}
  next : ∀ time n, Step (leader time n) (event time n) (state time n) (state (time + 1) n)

def EventuallyFrom (start : Nat) (p : Nat → Prop) : Prop :=
  ∃ time, start ≤ time ∧ p time

theorem propagate {p : Nat → Prop} (next : ∀ t, p t → p (t + 1))
    {a b : Nat} (order : a ≤ b) (ha : p a) : p b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le order
  clear order
  induction d with
  | zero => simpa using ha
  | succ d ih => exact next _ ih

namespace Step

theorem requests {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t) :
    Requests.Step s.requests t.requests := by
  cases h with
  | handle_request => exact .handle _ _ _ _
  | resume_request => exact .resume _ _ _ (by assumption) (by assumption)
  | _ => exact .stutter _

theorem invariant {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t)
    (hs : LocalInvariant s.delivery) : LocalInvariant t.delivery := by
  cases h with
  | handle_learn => exact handle_learn_invariant hs _ _
  | _ => exact hs

theorem completed {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t)
    (hs : LocalInvariant s.delivery) (hc : Completed s.delivery) : Completed t.delivery := by
  cases h with
  | handle_learn => exact handle_learn_completed hs hc _ _
  | _ => exact hc

theorem log_preserved {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t)
    {index : Nat} {entry : Item Request Response} (recorded : s.delivery.log index = some entry) :
    t.delivery.log index = some entry := by
  cases h with
  | handle_learn => exact handle_learn_log_preserved _ _ _ recorded
  | _ => exact recorded

theorem log_origin {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t)
    {index : Nat} {entry : Item Request Response} (recorded : t.delivery.log index = some entry) :
    s.delivery.log index = some entry ∨ event = .handle_learn index entry := by
  cases h with
  | handle_learn =>
      rcases handle_learn_log_origin _ _ _ recorded with old | ⟨rfl, rfl⟩
      · exact Or.inl old
      · exact Or.inr rfl
  | _ => exact Or.inl recorded

theorem delivery_prefix {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t) :
    s.delivery.delivered <+: t.delivery.delivered := by
  cases h with
  | handle_learn => exact handle_learn_delivery_prefix _ _ _
  | _ => exact List.prefix_refl _

theorem proposal_origin {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t)
    {item : Item Request Response} (member : item ∈ t.requests.proposals) :
    item ∈ s.requests.proposals ∨ event = .resume_request item.1 item.2 := by
  cases h with
  | handle_request =>
      simp only [Requests.handle_request] at member
      split at member
      · exact Or.inl member
      · split at member <;> exact Or.inl member
  | resume_request =>
      rcases List.mem_cons.mp member with rfl | old
      · exact Or.inr rfl
      · exact Or.inl old
  | _ => exact Or.inl member

theorem request_issued {s t : Replica Request Payload Response}
    {request : Request} {payload : Payload}
    (h : Step true (.handle_request request payload) s t) :
    Requests.Issued t.requests request := by
  cases h
  exact Requests.handle_request_issued _ _ _

theorem resume_proposed {s t : Replica Request Payload Response}
    {leader : Bool} {request : Request} {response : Response}
    (h : Step leader (.resume_request request response) s t) :
    (request, response) ∈ t.requests.proposals := by
  cases h
  exact List.mem_cons_self

theorem learn_result {s t : Replica Request Payload Response}
    {leader : Bool} {index : Nat} {entry : Item Request Response}
    (h : Step leader (.handle_learn index entry) s t) :
    t.delivery = Resdet.handle_learn s.delivery index entry := by
  cases h
  rfl

end Step

namespace Execution

variable (run : Execution Node Request Payload Response)

theorem invariant (time : Nat) (n : Node) : LocalInvariant (run.state time n).delivery := by
  induction time with
  | zero => simpa [run.initial] using (initialLocal_invariant (Request := Request) (Response := Response))
  | succ time ih => exact (run.next time n).invariant ih

theorem completed (time : Nat) (n : Node) : Completed (run.state time n).delivery := by
  induction time with
  | zero => simpa [run.initial] using (initialLocal_completed (Request := Request) (Response := Response))
  | succ time ih => exact (run.next time n).completed (run.invariant time n) ih

theorem request_invariant (time : Nat) (n : Node) : Requests.Invariant (run.state time n).requests := by
  induction time with
  | zero => simpa [run.initial] using (Requests.initial_invariant (Request := Request)
      (Payload := Payload) (Response := Response))
  | succ time ih => exact Requests.step_preserves_invariant ih (run.next time n).requests

theorem log_mono (n : Node) {a b index : Nat} {entry : Item Request Response}
    (order : a ≤ b) (recorded : (run.state a n).delivery.log index = some entry) :
    (run.state b n).delivery.log index = some entry :=
  propagate (fun time present => (run.next time n).log_preserved present) order recorded

theorem log_origin (time : Nat) (n : Node) {index : Nat} {entry : Item Request Response}
    (recorded : (run.state time n).delivery.log index = some entry) :
    ∃ earlier, earlier < time ∧ run.event earlier n = .handle_learn index entry := by
  induction time with
  | zero => simp [run.initial, initialLocal] at recorded
  | succ time ih =>
      rcases (run.next time n).log_origin recorded with old | event
      · obtain ⟨earlier, before, origin⟩ := ih old
        exact ⟨earlier, by omega, origin⟩
      · exact ⟨time, Nat.lt_succ_self _, event⟩

theorem proposal_origin (time : Nat) (n : Node) {item : Item Request Response}
    (member : item ∈ (run.state time n).requests.proposals) :
    ∃ earlier, earlier < time ∧ run.event earlier n = .resume_request item.1 item.2 := by
  induction time with
  | zero => simp [run.initial] at member
  | succ time ih =>
      rcases (run.next time n).proposal_origin member with old | event
      · obtain ⟨earlier, before, origin⟩ := ih old
        exact ⟨earlier, by omega, origin⟩
      · exact ⟨time, Nat.lt_succ_self _, event⟩

theorem request_event_issued (time : Nat) (n : Node) (request : Request) (payload : Payload)
    (leader : run.leader time n = true)
    (event : run.event time n = .handle_request request payload) :
    Requests.Issued (run.state (time + 1) n).requests request := by
  have step := run.next time n
  rw [leader, event] at step
  exact step.request_issued

theorem resume_event_proposed (time : Nat) (n : Node) (request : Request) (response : Response)
    (event : run.event time n = .resume_request request response) :
    (request, response) ∈ (run.state (time + 1) n).requests.proposals := by
  have step := run.next time n
  rw [event] at step
  exact step.resume_proposed

theorem delivery_mono (n : Node) {a b : Nat} (order : a ≤ b) :
    (run.state a n).delivery.delivered <+: (run.state b n).delivery.delivered :=
  propagate (p := fun time => (run.state a n).delivery.delivered <+:
    (run.state time n).delivery.delivered)
    (fun time pre => pre.trans (run.next time n).delivery_prefix) order (List.prefix_refl _)

end Execution
end Resdet
