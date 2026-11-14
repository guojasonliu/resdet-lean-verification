import Resdet
import Tests
import ContractsTests
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
    `Resdet.deliver_consistent, `Resdet.deliver_append,
    `Resdet.Requests.step_preserves_invariant,
    `Resdet.handle_learn_invariant, `Resdet.handle_learn_completed,
    `Resdet.Execution.invariant, `Resdet.Execution.completed,
    `Resdet.lemma_1_same_processed_entry, `Resdet.lemma_2_no_hole_processing,
    `Resdet.theorem_1_safety, `Resdet.theorem_1_on_execution,
    `Resdet.lemma_3_eventual_agreement, `Resdet.lemma_4_eventual_prefix_learning,
    `Resdet.lemma_5_eventual_delivery, `Resdet.lemma_5_on_execution,
    `Resdet.theorem_2_liveness, `Resdet.delivered_permanently_once,
    `Resdet.Tests.out_of_order_waits, `Resdet.Tests.filling_gap_drains_prefix,
    `Resdet.Tests.duplicate_callback_ignored, `Resdet.Tests.nonleader_forwards_payload,
    `Resdet.Tests.duplicate_request_does_not_reexecute,
    `Resdet.Tests.both_proposals_after_demotion,
    `Resdet.Tests.later_leader_retries_suppressed,
    `Resdet.ContractsTests.consensus_contract, `Resdet.ContractsTests.request_progress,
    `Resdet.ContractsTests.leader_admission, `Resdet.ContractsTests.former_leader_progress,
    `Resdet.ContractsTests.concrete_delivery, `Resdet.ContractsTests.safety_instance,
    `Resdet.ContractsTests.liveness_instance]
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

#print axioms Resdet.theorem_1_on_execution
#print axioms Resdet.theorem_2_liveness
#print axioms Resdet.ContractsTests.liveness_instance
