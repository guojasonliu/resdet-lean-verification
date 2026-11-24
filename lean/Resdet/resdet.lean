import Resdet.dedup

/-!
Section 4: state, delivery deduplication, and the paper's handlers.
The final section defines executions of those handlers for Section 5.
Consensus guarantees and liveness assumptions are in their named files.
`safety.lean` and `liveness.lean` each contain their supporting invariants
and numbered paper proofs.
-/

/-! ## Delivery state and helper -/
namespace Resdet

structure DeliveryState (Request Response : Type) where
  seen : List Request := []
  delivered : List (Item Request Response) := []
  deriving DecidableEq

variable {Request Response : Type} [DecidableEq Request]

/-- Deliver the first response for each unseen ID, preserving item order. -/
def deliver (items : List (Item Request Response)) (s : DeliveryState Request Response) :
    DeliveryState Request Response :=
  let fresh := dedupFrom s.seen items
  { seen := s.seen ++ fresh.map Prod.fst, delivered := s.delivered ++ fresh }

end Resdet

/-!
The paper's Resdet pseudocode. Consensus, transport, and downstream RPCs are
external effects. The request handler is split at the blocking RPC; its response
continuation does not recheck leadership. Learning and processing use each
replica's own log, with one-based indices.

`calls`, `forwarded`, and `proposals` record external effects. An RPC stays in
`pending` until its response arrives, then in `returned` until the handler resumes.
Locally numbered attempts distinguish concurrent retries for the same request.
Consensus sees only the request ID and response. `history` records processed entries.
-/

namespace Resdet.Requests

structure State (Request Payload Response : Type) where
  calls : List (Request × Payload) := []
  forwarded : List (Request × Payload) := []
  proposals : List (Item Request Response) := []
  pending : List (Nat × Request) := []
  returned : List (Nat × Request × Response) := []
  deriving DecidableEq

variable {Request Payload Response : Type} [DecidableEq Request]

def forward (request : Request) (payload : Payload) (s : State Request Payload Response) :=
  { s with forwarded := (request, payload) :: s.forwarded }

/-- Each call gets its own continuation, including retries of the same request. -/
def send_and_recv (request : Request) (payload : Payload)
    (s : State Request Payload Response) :=
  { s with calls := (request, payload) :: s.calls
           pending := (s.calls.length, request) :: s.pending }

def propose (entry : Item Request Response) (s : State Request Payload Response) :=
  { s with proposals := entry :: s.proposals }

def handle_request (isLeader : Bool) (request : Request) (payload : Payload)
    (s : State Request Payload Response) : State Request Payload Response :=
  if !isLeader then forward request payload s
  else send_and_recv request payload s

def rpc_return (attempt : Nat) (request : Request) (response : Response)
    (s : State Request Payload Response) :=
  { s with pending := s.pending.erase (attempt, request)
           returned := (attempt, request, response) :: s.returned }

def resume_request (attempt : Nat) (request : Request) (response : Response)
    (s : State Request Payload Response) :=
  propose (request, response) { s with returned := s.returned.filter (·.1 != attempt) }

end Resdet.Requests

namespace Resdet

structure LocalState (Request Response : Type) extends DeliveryState Request Response where
  log : Nat → Option (Item Request Response) := fun _ => none
  learned : Nat := 0
  processed : Nat := 0
  history : List (Item Request Response) := []

variable {Request Response : Type} [DecidableEq Request]

def initialLocal : LocalState Request Response := {}

/-- One iteration of `process`, after finding the next local entry. -/
def processEntry (s : LocalState Request Response) (entry : Item Request Response) :=
  { s with processed := s.processed + 1
           history := s.history ++ [entry]
           toDeliveryState := deliver [entry] s.toDeliveryState }

/-- Fuel is the finite distance to the current learned high-water mark. -/
def processLoop : Nat → LocalState Request Response → LocalState Request Response
  | 0, s => s
  | fuel + 1, s =>
      if s.processed + 1 ≤ s.learned then
        match s.log (s.processed + 1) with
        | none => s
        | some entry => processLoop fuel (processEntry s entry)
      else s

def process (s : LocalState Request Response) : LocalState Request Response :=
  processLoop (s.learned - s.processed) s

def recordLearn (s : LocalState Request Response) (index : Nat)
    (entry : Item Request Response) : LocalState Request Response :=
  { s with log := fun k => if k = index then some entry else s.log k
           learned := max s.learned index }

def handle_learn (s : LocalState Request Response) (index : Nat)
    (entry : Item Request Response) : LocalState Request Response :=
  match s.log index with
  | some _ => s
  | none => process (recordLearn s index entry)

end Resdet

/-! ## Executions of the handlers

Each replica has its own log. Events serialize nonblocking local updates.
An RPC can wait between request and response events. Likewise, a received
learn callback can wait before its handler updates the local log.
State is preserved within an incarnation; reset and recovery are not modeled.
-/
namespace Resdet

structure Replica (Request Payload Response : Type) where
  requests : Requests.State Request Payload Response := {}
  delivery : LocalState Request Response := initialLocal

inductive Event (Request Payload Response : Type)
  | submit_request (request : Request) (payload : Payload)
  | handle_request (request : Request) (payload : Payload)
  | rpc_return (attempt : Nat) (request : Request) (response : Response)
  | resume_request (attempt : Nat) (request : Request) (response : Response)
  | receive_learn (index : Nat) (entry : Item Request Response)
  | handle_learn (receivedAt index : Nat) (entry : Item Request Response)
  | idle
  deriving DecidableEq

variable {Node Request Payload Response : Type} [DecidableEq Request]

/-- Submission is an observation at the service. An RPC return enables its
matching continuation; a learn receipt precedes the callback's local update. -/
inductive Step (isLeader : Bool) : Event Request Payload Response →
    Replica Request Payload Response → Replica Request Payload Response → Prop
  | submit_request (s) (request payload) : Step isLeader (.submit_request request payload) s s
  | handle_request (s) (request payload) :
      Step isLeader (.handle_request request payload) s
        { s with requests := Requests.handle_request isLeader request payload s.requests }
  | rpc_return (s) (attempt : Nat) (request response)
      (pending : (attempt, request) ∈ s.requests.pending) :
      Step isLeader (.rpc_return attempt request response) s
        { s with requests := Requests.rpc_return attempt request response s.requests }
  | resume_request (s) (attempt : Nat) (request response)
      (returned : (attempt, request, response) ∈ s.requests.returned) :
      Step isLeader (.resume_request attempt request response) s
        { s with requests := Requests.resume_request attempt request response s.requests }
  | receive_learn (s) (index entry) : Step isLeader (.receive_learn index entry) s s
  | handle_learn (s) (receivedAt index entry) :
      Step isLeader (.handle_learn receivedAt index entry) s
        { s with delivery := handle_learn s.delivery index entry }
  | idle (s) : Step isLeader .idle s s

/-- Network observations for L2, indexed by time, sender, recipient, and message. -/
structure NetworkTrace (Node : Type) where
  Message : Type
  sent : Nat → Node → Node → Message → Prop
  received : Nat → Node → Node → Message → Prop

structure Execution (Node Request Payload Response : Type) [DecidableEq Request] where
  state : Nat → Node → Replica Request Payload Response
  leader : Nat → Node → Bool
  event : Nat → Node → Event Request Payload Response
  network : NetworkTrace Node
  initial : ∀ n, state 0 n = {}
  next : ∀ time n, Step (leader time n) (event time n) (state time n) (state (time + 1) n)
  /-- A completed learn handler refers to its own earlier invocation. -/
  learnInvoked : ∀ time n receivedAt index entry,
    event time n = .handle_learn receivedAt index entry →
    receivedAt < time ∧ event receivedAt n = .receive_learn index entry

def EventuallyFrom (start : Nat) (p : Nat → Prop) : Prop :=
  ∃ time, start ≤ time ∧ p time

end Resdet
