import Resdet
import ProtocolTests

namespace Resdet.Paper.Tests

def ordered : List (Item Nat Nat) := [(10, 1), (20, 2), (10, 99), (30, 3), (20, 77)]
def batched : List (List (Item Nat Nat)) :=
  [[(10, 1), (20, 2)], [], [(10, 99)], [(30, 3), (20, 77)]]

theorem batch_boundaries_do_not_change_result :
    applyBatches batched {} = applyBatches (ordered.map (fun item => [item])) {} :=
  rebatching_preserves_delivery (by decide) {}

theorem first_not_last_response :
    applyBatches batched {} =
      { seen := [10, 20, 30], delivered := [(10, 1), (20, 2), (30, 3)] } ∧
    firstFor 10 ordered = some (10, 1) := by decide

theorem recovered_delivery_is_first_committed :
    firstFor 1 Protocol.Tests.p15.core.log.flatten = some (1, 9) :=
  first_committed_response (Protocol.reachable_refines Protocol.Tests.recovery_run)
    false (by decide)

/-- The retained-state recovery trace satisfies the paper-shaped contracts.
It does not model loss of volatile state or handler reconstruction on recovery. -/
theorem paper_contracts_satisfiable :
    ∃ (tr : Nat → Protocol.Tests.S) (finish : Nat),
      Protocol.Behavior Protocol.Tests.cfg false tr ∧
      Protocol.StableLeader tr true finish ∧
      Protocol.Received (tr finish) 1 ∧
      PendingHandlers tr true 1 ∧
      Protocol.StableConsensusProgress tr true finish ∧
      ∀ r, DeliveryProgress (fun t => (tr t).core) r := by
  obtain ⟨tr, finish, b, stable, ready, handlers, consensus, delivery⟩ :=
    Protocol.Tests.retry_contracts_satisfiable
  exact ⟨tr, finish, b, stable, ready, .ofRetry handlers, consensus, delivery⟩

/-- A small regression for recovery that keeps a request marker but loses its
unfinished handler. Repeated arrivals then stop at the duplicate check.
This is outside the retained-state model: it explains why a recovery model
must account for handler reconstruction, not a failure of the proved protocol. -/
structure Admission where
  seen : List Nat := []
  running : List Nat := []
  proposals : List Nat := []
  deriving DecidableEq

def receive (s : Admission) (request : Nat) : Admission :=
  if request ∈ s.seen then s
  else { s with seen := request :: s.seen, running := request :: s.running }

def crashDroppingHandler (s : Admission) : Admission := { s with running := [] }
def stranded : Admission := crashDroppingHandler (receive {} 1)

def retryRequests : Nat → Admission
  | 0 => stranded
  | count + 1 => receive (retryRequests count) 1

theorem recovery_marker_counterexample (count : Nat) :
    retryRequests count = stranded := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [retryRequests, ih] using (show receive stranded 1 = stranded by decide)

theorem retries_without_resumption_stay_pending (count : Nat) :
    1 ∈ (retryRequests count).seen ∧ (retryRequests count).running = [] ∧
      (retryRequests count).proposals = [] := by
  rw [recovery_marker_counterexample]
  decide

end Resdet.Paper.Tests
