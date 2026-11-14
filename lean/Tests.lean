import Resdet.Assumptions
import Resdet.RequestProofs

/-!
Kernel-checked examples of the paper's handlers. These complement the general
proofs. The demotion example checks a finite request-handler execution. Its
leaders cannot both be nonfaulty under the fault model used in the liveness proof.
-/
namespace Resdet.Tests

abbrev Replica := LocalState Nat Nat

def emptyReplica : Replica := initialLocal
def learnedSecond := handle_learn emptyReplica 2 (1, 99)
def learnedThird := handle_learn learnedSecond 3 (2, 20)
def filledGap := handle_learn learnedThird 1 (1, 10)

theorem out_of_order_waits :
    learnedThird.learned = 3 ∧ learnedThird.processed = 0 ∧
      learnedThird.log 2 = some (1, 99) ∧ learnedThird.delivered = [] := by decide

theorem filling_gap_drains_prefix :
    filledGap.processed = 3 ∧ filledGap.history = [(1, 10), (1, 99), (2, 20)] ∧
      filledGap.seen = [1, 2] ∧ filledGap.delivered = [(1, 10), (2, 20)] := by decide

/-- Even a conflicting duplicate callback cannot replace the first local entry. -/
theorem duplicate_callback_ignored : handle_learn filledGap 1 (1, 777) = filledGap := rfl

theorem local_handler_invariant : LocalInvariant filledGap :=
  handle_learn_invariant
    (handle_learn_invariant (handle_learn_invariant initialLocal_invariant 2 (1, 99))
      3 (2, 20)) 1 (1, 10)

theorem delivery_ids_unique : (filledGap.delivered.map Prod.fst).Nodup :=
  at_most_once_delivery local_handler_invariant

def inOrder := handle_learn (handle_learn (handle_learn emptyReplica 1 (1, 10))
  2 (1, 99)) 3 (2, 20)

theorem callback_order_does_not_change_delivery :
    inOrder.delivered = filledGap.delivered := by decide

theorem dedup_respects_seen :
    dedupFrom [2] [(2, 99), (1, 7), (1, 9), (3, 10), (2, 100)] =
      [(1, 7), (3, 10)] := by decide

abbrev RequestState := Requests.State Nat Nat Nat

def forwarded : RequestState := Requests.handle_request false 1 42 {}

theorem nonleader_forwards_payload :
    forwarded.forwarded = [(1, 42)] ∧ forwarded.calls = [] ∧
      forwarded.proposals = [] := by decide

def accepted : RequestState := Requests.handle_request true 1 42 {}

theorem duplicate_request_does_not_reexecute :
    Requests.handle_request true 1 42 accepted = accepted := by decide

/-- `false` names A and `true` names B. These are handler snapshots, not a
claim that either demoted node remains nonfaulty. -/
structure TwoNodes where
  leader : Bool := false
  a : RequestState := {}
  b : RequestState := {}

def c0 : TwoNodes := {}
def c1 : TwoNodes := { c0 with a := Requests.handle_request (!c0.leader) 1 42 c0.a }
def c2 : TwoNodes := { c1 with leader := true }
def c3 : TwoNodes := { c2 with a := Requests.resume_request 1 7 c2.a }
def c4 : TwoNodes := { c3 with b := Requests.handle_request c3.leader 1 42 c3.b }
def c5 : TwoNodes := { c4 with leader := false }
def c6 : TwoNodes := { c5 with b := Requests.resume_request 1 9 c5.b }

theorem a_handler_steps : Requests.Step c0.a c1.a ∧ Requests.Step c2.a c3.a := by
  constructor
  · exact .handle c0.a (!c0.leader) 1 42
  · exact .resume c2.a 1 7 (by change 1 ∈ ([1] : List Nat); decide)
      (by change ¬ 1 ∈ ([] : List Nat); decide)

theorem b_handler_steps : Requests.Step c3.b c4.b ∧ Requests.Step c5.b c6.b := by
  constructor
  · exact .handle c3.b c3.leader 1 42
  · exact .resume c5.b 1 9 (by change 1 ∈ ([1] : List Nat); decide)
      (by change ¬ 1 ∈ ([] : List Nat); decide)

/-- The code proposes after the RPC even when the accepting leader was demoted. -/
theorem both_proposals_after_demotion :
    c2.leader ≠ false ∧ c5.leader ≠ true ∧
      c6.a.proposals = [(1, 7)] ∧ c6.b.proposals = [(1, 9)] := by decide

/-- Neither replica retries its completed call when it next handles rid as leader.
If consensus drops the follower proposals, request deduplication alone cannot
produce another proposal. This schedule is outside the nonfaulty-leader case. -/
theorem later_leader_retries_suppressed :
    Requests.handle_request true 1 42 c6.a = c6.a ∧
      Requests.handle_request true 1 42 c6.b = c6.b ∧
      c6.a.calls = [(1, 42)] ∧ c6.b.calls = [(1, 42)] := by decide

/-- Under the clarified fault model, the two observed demotions exclude both
nodes from the nonfaulty set. The handler snapshots are not a counterexample
to liveness for nonfaulty replicas. -/
theorem demotions_exclude_nonfaulty
    (run : Execution Bool Nat Nat Nat) (nonfaulty : Bool → Prop)
    (faults : FaultModel run nonfaulty)
    (aLeader : run.leader 0 false = true)
    (aDemoted : run.leader 1 false = false)
    (bLeader : run.leader 1 true = true)
    (bDemoted : run.leader 2 true = false) :
    ¬ nonfaulty false ∧ ¬ nonfaulty true := by
  constructor
  · intro hn
    have retained := faults.retainsLeadership 0 1 false hn (by decide) aLeader
    rw [aDemoted] at retained
    contradiction
  · intro hn
    have retained := faults.retainsLeadership 1 2 true hn (by decide) bLeader
    rw [bDemoted] at retained
    contradiction

end Resdet.Tests
