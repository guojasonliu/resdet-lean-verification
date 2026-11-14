import Resdet.Assumptions

namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]
variable (run : Execution Node Request Payload Response)
variable {nonfaulty : Node → Prop} {agreed : Nat → Nat → Item Request Response → Prop}

/-- CG3(1), request submission/handling progress, and the fault model together
put a pending invocation in the leader branch of `handle_request`. -/
theorem leader_admission (faults : FaultModel run nonfaulty)
    (consensus : Consensus run nonfaulty agreed) {submitted : Request → Prop}
    (submissions : SubmissionProgress run nonfaulty agreed submitted)
    (request : Request) (submittedRequest : submitted request)
    (pending : ¬ ∃ time index response, 1 ≤ index ∧ agreed time index (request, response)) :
    ∃ time n payload, nonfaulty n ∧ run.leader time n = true ∧
      run.event time n = .handle_request request payload := by
  obtain ⟨start, n, hn, leader⟩ := consensus.election
  obtain ⟨time, payload, afterStart, event⟩ :=
    submissions.handleRequest start n request submittedRequest hn leader pending
  exact ⟨time, n, payload, hn, faults.retainsLeadership start time n hn afterStart leader, event⟩

/-- A non-faulty handler retains leadership through its RPC, so CG3(2) applies. -/
theorem proposal_event_eventually_agreed (faults : FaultModel run nonfaulty)
    (consensus : Consensus run nonfaulty agreed)
    (time : Nat) (n : Node) (request : Request) (response : Response)
    (hn : nonfaulty n) (event : run.event time n = .resume_request request response) :
    ∃ later index, time ≤ later ∧ 1 ≤ index ∧ agreed later index (request, response) :=
  consensus.currentLeaderProgress time n request response hn
    (run.resume_is_leader faults time n request response hn event) event

/-- Lemma 3: CG3(1) and L1/L2/L4 yield leader handling; L3/L4 yields its
response continuation, and CG3(2) yields agreement. Leadership retention is the
fault-model rule, rather than an extra promise to agree former-leader proposals. -/
theorem lemma_3_eventual_agreement (faults : FaultModel run nonfaulty)
    (consensus : Consensus run nonfaulty agreed)
    {submitted : Request → Prop} (submissions : SubmissionProgress run nonfaulty agreed submitted)
    (handlers : RequestProgress run nonfaulty)
    (request : Request) (submittedRequest : submitted request) :
    ∃ time index response, 1 ≤ index ∧ agreed time index (request, response) := by
  classical
  by_cases done : ∃ time index response, 1 ≤ index ∧ agreed time index (request, response)
  · exact done
  obtain ⟨time, n, payload, hn, leader, event⟩ :=
    leader_admission run faults consensus submissions request submittedRequest done
  have issued := run.request_event_issued time n request payload leader event
  by_cases proposed : Requests.Proposed (run.state (time + 1) n).requests request
  · obtain ⟨⟨rid, response⟩, member, same⟩ := List.mem_map.mp proposed
    change rid = request at same
    subst rid
    obtain ⟨earlier, _, resume⟩ := run.proposal_origin (time + 1) n member
    obtain ⟨later, index, _, positive, committed⟩ :=
      proposal_event_eventually_agreed run faults consensus earlier n request response hn resume
    exact ⟨later, index, response, positive, committed⟩
  · obtain ⟨resumeTime, response, _, resume⟩ := handlers.resume (time + 1) n request hn issued proposed
    obtain ⟨later, index, _, positive, committed⟩ :=
      proposal_event_eventually_agreed run faults consensus resumeTime n request response hn resume
    exact ⟨later, index, response, positive, committed⟩

/-- A callback already recorded need not be invoked again. Otherwise its actual
execution records the agreed entry; duplicate callbacks are handled using CG1. -/
theorem agreed_eventually_recorded (consensus : Consensus run nonfaulty agreed)
    (start index : Nat) (entry : Item Request Response) (positive : 1 ≤ index)
    (committed : agreed start index entry) (n : Node) (hn : nonfaulty n) :
    EventuallyFrom start (fun time => (run.state time n).delivery.log index = some entry) := by
  rcases consensus.learnCallbacks start index entry positive committed n hn with old | later
  · exact ⟨start, Nat.le_refl _, old⟩
  · obtain ⟨time, afterStart, event⟩ := later
    exact ⟨time + 1, by omega,
      run.learn_event_recorded consensus.indexAgreement time n hn index entry positive event⟩

theorem finite_prefix_eventually_recorded (consensus : Consensus run nonfaulty agreed)
    (start count : Nat) (n : Node) (hn : nonfaulty n)
    (available : ∀ index, 1 ≤ index → index ≤ count → ∃ entry, agreed start index entry) :
    EventuallyFrom start (fun time => PrefixPresent (run.state time n).delivery count) := by
  induction count with
  | zero => exact ⟨start, Nat.le_refl _, by intro index positive before; omega⟩
  | succ count ih =>
      obtain ⟨a, ha, earlier⟩ := ih (fun index positive before => available index positive (by omega))
      obtain ⟨entry, committed⟩ := available (count + 1) (by omega) (Nat.le_refl _)
      obtain ⟨b, hb, last⟩ := agreed_eventually_recorded run consensus start (count + 1)
        entry (by omega) committed n hn
      refine ⟨max a b, by omega, ?_⟩
      intro index positive before
      by_cases eq : index = count + 1
      · subst index
        exact ⟨entry, run.log_mono n (Nat.le_max_right _ _) last⟩
      · obtain ⟨old, recorded⟩ := earlier index positive (by omega)
        exact ⟨old, run.log_mono n (Nat.le_max_left _ _) recorded⟩

/-- Lemma 4: every non-faulty replica eventually records the agreed prefix,
including the specified response entry at its final index. -/
theorem lemma_4_eventual_prefix_learning (consensus : Consensus run nonfaulty agreed)
    (start index : Nat) (entry : Item Request Response) (positive : 1 ≤ index)
    (committed : agreed start index entry) (n : Node) (hn : nonfaulty n) :
    EventuallyFrom start (fun time => PrefixPresent (run.state time n).delivery index ∧
      (run.state time n).delivery.log index = some entry) := by
  obtain ⟨a, ha, prefixPresent⟩ := finite_prefix_eventually_recorded run consensus start index n hn
    (consensus.prefixAgreement start index entry committed)
  obtain ⟨b, hb, last⟩ := agreed_eventually_recorded run consensus start index entry positive committed n hn
  refine ⟨max a b, by omega, ?_, run.log_mono n (Nat.le_max_right _ _) last⟩
  intro k hk before
  obtain ⟨value, recorded⟩ := prefixPresent k hk before
  exact ⟨value, run.log_mono n (Nat.le_max_left _ _) recorded⟩

/-- Lemma 5 on executions: `handle_learn` already completed its `process` loop,
so a present contiguous prefix has already produced a response for this ID. -/
theorem lemma_5_on_execution (time : Nat) (n : Node) (index : Nat)
    (entry : Item Request Response) (positive : 1 ≤ index)
    (prefixPresent : PrefixPresent (run.state time n).delivery index)
    (recorded : (run.state time n).delivery.log index = some entry) :
    ∃ response, (entry.1, response) ∈ (run.state time n).delivery.delivered :=
  lemma_5_eventual_delivery (run.invariant time n) (run.completed time n) positive prefixPresent recorded

/-- Theorem 2: the three numbered liveness lemmas compose into eventual delivery.
The fault model makes the leadership interpretation explicit. CG1 is also used
when a callback finds an already-recorded entry; see the paper correspondence. -/
theorem theorem_2_liveness (faults : FaultModel run nonfaulty)
    (consensus : Consensus run nonfaulty agreed)
    {submitted : Request → Prop} (submissions : SubmissionProgress run nonfaulty agreed submitted)
    (handlers : RequestProgress run nonfaulty) :
    ∀ request, submitted request → ∀ n, nonfaulty n →
      EventuallyFrom 0 (fun time => ∃ response,
        (request, response) ∈ (run.state time n).delivery.delivered) := by
  intro request submittedRequest n hn
  obtain ⟨agreedTime, index, response, positive, committed⟩ :=
    lemma_3_eventual_agreement run faults consensus submissions handlers request submittedRequest
  obtain ⟨learnedTime, _, prefixPresent, recorded⟩ :=
    lemma_4_eventual_prefix_learning run consensus agreedTime index (request, response) positive committed n hn
  obtain ⟨delivered, member⟩ :=
    lemma_5_on_execution run learnedTime n index (request, response) positive prefixPresent recorded
  exact ⟨learnedTime, Nat.zero_le _, delivered, member⟩

/-- Delivery persists and remains unique; the theorem concerns delivery to
service code, not exactly-once physical execution at the downstream service. -/
theorem delivered_permanently_once (time : Nat) (n : Node) (request : Request) (response : Response)
    (member : (request, response) ∈ (run.state time n).delivery.delivered) :
    ∀ later, time ≤ later →
      (request, response) ∈ (run.state later n).delivery.delivered ∧
      ((run.state later n).delivery.delivered.map Prod.fst).count request = 1 := by
  intro later afterTime
  have retained := (run.delivery_mono n afterTime).subset member
  refine ⟨retained, ?_⟩
  have idMember : request ∈ (run.state later n).delivery.delivered.map Prod.fst :=
    List.mem_map_of_mem retained
  have positive := List.count_pos_iff.mpr idMember
  have bound := List.nodup_iff_count.mp (at_most_once_delivery (run.invariant later n)) request
  omega

end Resdet
