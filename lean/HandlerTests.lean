import Resdet

/-!
Kernel-checked examples of out-of-order learning, delivery deduplication, and
overlapping physical invocations for one logical request.
-/
namespace Resdet.HandlerTests

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

def retried := Requests.handle_request true 1 42 accepted
def secondReturnsFirst := Requests.resume_request 1 1 9 retried
def bothReturned := Requests.resume_request 0 1 7 secondReturnsFirst

/-- The same leader issues two physical calls for rid 1. -/
theorem retry_issues_another_call :
    retried.calls = [(1, 42), (1, 42)] ∧
      (0, 1) ∈ retried.pending ∧ (1, 1) ∈ retried.pending := by decide

/-- Completing the retry leaves the original RPC in flight. Both may propose. -/
theorem overlapping_retries_complete_independently :
    secondReturnsFirst.pending = [(0, 1)] ∧ bothReturned.pending = [] ∧
    bothReturned.proposals = [(1, 7), (1, 9)] := by decide

end Resdet.HandlerTests
