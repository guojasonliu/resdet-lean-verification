import Resdet
import Tests
import Lean

/-!
Reject extra axioms transitively, including unfinished proofs and native
evaluation axioms. Protocol assumptions are in the model, not added axioms.
Only Lean's standard logical foundations are allowed here.
-/
open Lean Elab Command in
run_cmd do
  -- Public proof entry points and regression witnesses must be imported.
  -- Every Resdet declaration is audited below, not just this list.
  let required := #[
    `Resdet.dedupFrom_append, `Resdet.dedupFrom_nodup,
    `Resdet.dedupFrom_fresh, `Resdet.dedupFrom_covers,
    `Resdet.applyWithDedup_correct,
    `Resdet.reachable_invariant, `Resdet.Protocol.reachable_refines,
    `Resdet.Protocol.all_safety,
    `Resdet.Paper.theorem_1_safety, `Resdet.Paper.theorem_2_liveness,
    `Resdet.Paper.theorem_1_crash_stop, `Resdet.Paper.theorem_2_crash_stop,
    `Resdet.Paper.first_committed_response, `Resdet.Paper.rebatching_preserves_delivery,
    `Resdet.Tests.sample_reachable, `Resdet.Tests.skipped_prefix_unreachable,
    `Resdet.Tests.early_delivery_unreachable,
    `Resdet.Tests.dedup_respects_seen, `Resdet.Tests.delivery_dedup_across_batches,
    `Resdet.Protocol.Tests.recovery_run,
    `Resdet.Protocol.Tests.single_arrival_enables_dispatch,
    `Resdet.Protocol.Tests.dispatch_before_receipt_unreachable,
    `Resdet.Protocol.Tests.repeated_arrival_keeps_one_dispatch,
    `Resdet.Protocol.Tests.pending_at_stabilization,
    `Resdet.Protocol.Tests.stable_leader_attempts_pending_request,
    `Resdet.Protocol.Tests.retry_contracts_satisfiable,
    `Resdet.Protocol.Tests.fairness_is_necessary,
    `Resdet.Paper.Tests.recovery_marker_counterexample,
    `Resdet.Paper.CrashStopTests.failover_retry_run,
    `Resdet.Paper.CrashStopTests.crash_stop_contracts_satisfiable]
  for name in required do
    let _ ← getConstInfo name
  let allowed := #[`propext, `Quot.sound, `Classical.choice]
  let mut checked := 0
  for (name, _) in (← getEnv).constants.toList do
    if `Resdet |>.isPrefixOf name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
      checked := checked + 1
  if checked == 0 then throwError "No Resdet declarations were audited"
  logInfo m!"Axiom audit passed for {checked} Resdet declarations (including tests)."

#print axioms Resdet.Paper.theorem_1_safety
#print axioms Resdet.Paper.theorem_2_liveness
#print axioms Resdet.Paper.theorem_1_crash_stop
#print axioms Resdet.Paper.theorem_2_crash_stop
