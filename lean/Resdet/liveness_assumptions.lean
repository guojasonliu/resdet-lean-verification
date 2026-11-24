import Resdet.consensus_assumptions

/-! Section 5.1. The service, network, downstream RPC, and local scheduler
supply the four liveness assumptions. -/
namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]

/-- Service code submitted this logical request at least once. -/
def Submitted (run : Execution Node Request Payload Response) (request : Request) : Prop :=
  ∃ time n payload, run.event time n = .submit_request request payload

/-- L1. While a logical request remains pending, service code repeatedly
submits it and a non-faulty leader accepts it. If it stays pending forever,
there is such a submission and acceptance after every cutoff. -/
def L1 (run : Execution Node Request Payload Response) (nonfaulty : Node → Prop) : Prop :=
  ∀ cutoff request, Submitted run request →
    (∀ time n response, nonfaulty n → (request, response) ∉ (run.state time n).delivery.delivered) →
    ∃ sentAt sender payload acceptedAt leader, cutoff ≤ sentAt ∧
      run.event sentAt sender = .submit_request request payload ∧ sentAt ≤ acceptedAt ∧
      nonfaulty leader ∧ run.leader acceptedAt leader = true ∧
      run.event acceptedAt leader = .handle_request request payload

/-- L2. A message repeatedly sent between non-faulty components is eventually
received. Sender, recipient, and message are the same for all attempts. -/
def L2 (run : Execution Node Request Payload Response) (nonfaulty : Node → Prop) : Prop :=
  ∀ sender receiver message, nonfaulty sender → nonfaulty receiver →
    (∀ cutoff, ∃ time, cutoff ≤ time ∧ run.network.sent time sender receiver message) →
    ∃ sentAt receivedAt, run.network.sent sentAt sender receiver message ∧
      sentAt ≤ receivedAt ∧ run.network.received receivedAt sender receiver message

/-- L3. Each nested request issued by a non-faulty leader returns a response.
The local call number identifies the attempt even across a change of leader. -/
def L3 (run : Execution Node Request Payload Response) (nonfaulty : Node → Prop) : Prop :=
  ∀ issuedAt n request payload, nonfaulty n → run.leader issuedAt n = true →
    run.event issuedAt n = .handle_request request payload →
    ∃ returnedAt response, issuedAt < returnedAt ∧ run.event returnedAt n =
      .rpc_return (run.state issuedAt n).requests.calls.length request response

/-- The remaining local work for a request whose RPC has returned or a learn
callback consensus has invoked. Each completion identifies its own invocation. -/
def completionOf (readyAt : Nat) : Event Request Payload Response → Option (Event Request Payload Response)
  | .rpc_return attempt request response => some (.resume_request attempt request response)
  | .receive_learn index entry => some (.handle_learn readyAt index entry)
  | _ => none

/-- L4. At a non-faulty replica, each runnable handler executes to completion.
The other nonblocking handler steps already complete in one protocol step. -/
def L4 (run : Execution Node Request Payload Response) (nonfaulty : Node → Prop) : Prop :=
  ∀ readyAt n completion, nonfaulty n →
    completionOf readyAt (run.event readyAt n) = some completion →
    ∃ time, readyAt < time ∧ run.event time n = completion

structure LivenessAssumptions (run : Execution Node Request Payload Response)
    (nonfaulty : Node → Prop) : Prop where
  l1 : L1 run nonfaulty
  l2 : L2 run nonfaulty
  l3 : L3 run nonfaulty
  l4 : L4 run nonfaulty

end Resdet
