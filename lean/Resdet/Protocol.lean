import Resdet.Delivery

/-!
The paper's Resdet pseudocode. Consensus, transport, and downstream RPCs are
external effects. The request handler is split at the blocking RPC; its response
continuation does not recheck leadership. Learning and processing use each
replica's own log, with one-based indices.

`calls`, `forwarded`, and `proposals` record external effects. `history` is ghost
proof instrumentation: handlers never consult it to select a response or branch.
-/

namespace Resdet.Requests

structure State (Request Payload Response : Type) where
  calls : List (Request × Payload) := []
  forwarded : List (Request × Payload) := []
  proposals : List (Item Request Response) := []
  deriving DecidableEq

variable {Request Payload Response : Type} [DecidableEq Request]

def Issued (s : State Request Payload Response) (request : Request) : Prop :=
  request ∈ s.calls.map Prod.fst

def Proposed (s : State Request Payload Response) (request : Request) : Prop :=
  request ∈ s.proposals.map Prod.fst

def forward (request : Request) (payload : Payload) (s : State Request Payload Response) :=
  { s with forwarded := (request, payload) :: s.forwarded }

/-- Begin the RPC; `resume_request` is its response continuation. -/
def send_and_recv (request : Request) (payload : Payload)
    (s : State Request Payload Response) :=
  { s with calls := (request, payload) :: s.calls }

def propose (entry : Item Request Response) (s : State Request Payload Response) :=
  { s with proposals := entry :: s.proposals }

def handle_request (isLeader : Bool) (request : Request) (payload : Payload)
    (s : State Request Payload Response) : State Request Payload Response :=
  if !isLeader then forward request payload s
  else if request ∈ s.calls.map Prod.fst then s
  else send_and_recv request payload s

def resume_request (request : Request) (response : Response)
    (s : State Request Payload Response) :=
  propose (request, response) s

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
