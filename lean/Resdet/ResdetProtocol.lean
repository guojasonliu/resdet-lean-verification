import Resdet.Safety

/-!
Resdet request handling above an abstract, append-only consensus log.
Arrival and forwarding are abstracted as a global received-request history,
retained across leaders. Crash/recovery changes availability, not recorded
events or delivery state. Request bodies are not tracked through execution.
-/
namespace Resdet.Protocol

structure Config where
  crashes : Bool := false

abbrev Dispatch (Node Request : Type) := Node × Request × Option Node
abbrev Execution (Node Request Response : Type) := Node × Request × Response

structure State (Node Request Payload Response : Type) where
  core : Resdet.State Node Request Response
  leader : Option Node
  up : Node → Bool
  requests : List (Item Request Payload)
  dispatches : List (Dispatch Node Request)
  executions : List (Execution Node Request Response)
  observed : List (Item Request Response)
  proposed : List (Item Request Response)

variable {Node Request Payload Response : Type}
variable [DecidableEq Node] [DecidableEq Request]

def initial (leader : Node) : State Node Request Payload Response :=
  ⟨Resdet.initial, some leader, fun _ => true, [], [], [], [], []⟩

/-- A nested invocation has arrived; network forwarding is abstracted away. -/
def Received (s : State Node Request Payload Response) (request : Request) : Prop :=
  ∃ payload, (request, payload) ∈ s.requests

inductive Step (cfg : Config) : State Node Request Payload Response →
    State Node Request Payload Response → Prop
  /-- Request arrivals, including retries, may repeat the same logical ID. -/
  | receive (s) (request payload) :
      Step cfg s { s with requests := (request, payload) :: s.requests }
  | dispatch (s) (n request) (leader : s.leader = some n) (live : s.up n = true)
      (received : Received s request)
      (fresh : ∀ l, (n, request, l) ∉ s.dispatches) :
      Step cfg s { s with dispatches := (n, request, s.leader) :: s.dispatches }
  | respond (s) (n request value)
      (dispatched : ∃ l, (n, request, l) ∈ s.dispatches)
      (fresh : ∀ v, (n, request, v) ∉ s.executions) :
      Step cfg s { s with
        executions := (n, request, value) :: s.executions
        observed := (request, value) :: s.observed }
  | propose (s) (n request value) (leader : s.leader = some n) (live : s.up n = true)
      (executed : (n, request, value) ∈ s.executions)
      (fresh : (request, value) ∉ s.proposed) :
      Step cfg s { s with proposed := (request, value) :: s.proposed }
  /-- A real proposal attempt by the current leader, even if an older leader
  buffered the same item. Required when CG3 covers only stable-leader attempts. -/
  | repropose (s) (n request value) (leader : s.leader = some n) (live : s.up n = true)
      (executed : (n, request, value) ∈ s.executions)
      (buffered : (request, value) ∈ s.proposed) :
      Step cfg s { s with proposed := (request, value) :: s.proposed }
  | decide (s) (batch : List (Item Request Response))
      (valid : ∀ item ∈ batch, item ∈ s.proposed) :
      Step cfg s { s with core := appendBatch s.core batch }
  | learn (s) (r slot) (live : s.up r = true) (valid : slot < s.core.log.length) :
      Step cfg s { s with core := learnSlot s.core r slot }
  | process (s) (r batch) (live : s.up r = true)
      (learned : (s.core.replica r).processed ∈ (s.core.replica r).learned)
      (entry : s.core.log[(s.core.replica r).processed]? = some batch) :
      Step cfg s { s with core := processBatch s.core r batch }
  | crash (s) (n) (enabled : cfg.crashes = true) (live : s.up n = true) :
      Step cfg s { s with
        up := fun r => if r = n then false else s.up r
        leader := if s.leader = some n then none else s.leader }
  | recover (s) (n) (enabled : cfg.crashes = true) (down : s.up n = false) :
      Step cfg s { s with up := fun r => if r = n then true else s.up r }
  | elect (s) (n) (enabled : cfg.crashes = true)
      (vacant : s.leader = none) (live : s.up n = true) :
      Step cfg s { s with leader := some n }
  | stutter (s) : Step cfg s s

inductive Reachable (cfg : Config) (leader : Node) : State Node Request Payload Response → Prop
  | init : Reachable cfg leader (initial leader)
  | step {s t} : Reachable cfg leader s → Step cfg s t → Reachable cfg leader t

/-- A proved forward simulation, not an assumed invariant in the full model. -/
theorem step_refines {cfg : Config} {s t : State Node Request Payload Response}
    (step : Step cfg s t) : Resdet.Step s.core t.core := by
  cases step with
  | decide batch _ => exact .append _ batch
  | learn r slot _ valid => exact .learn _ r slot valid
  | process r batch _ learned entry => exact .process _ r batch learned entry
  | _ => exact .stutter _

theorem reachable_refines {cfg : Config} {leader : Node}
    {s : State Node Request Payload Response} (h : Reachable cfg leader s) :
    Resdet.Reachable s.core := by
  induction h with
  | init => exact .init
  | step _ step ih => exact .step ih (step_refines step)

end Resdet.Protocol
