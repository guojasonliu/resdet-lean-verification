import Resdet.Assumptions

namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]
variable (run : Execution Node Request Payload Response)
variable {nonfaulty : Node → Prop} {agreed : Nat → Nat → Item Request Response → Prop}

/-- The actual proposal event may occur before or after the handler loses leadership. -/
theorem proposal_event_eventually_agreed (consensus : Consensus run nonfaulty agreed)
    (former : FormerLeaderProposalProgress run nonfaulty agreed)
    (time : Nat) (n : Node) (request : Request) (response : Response)
    (hn : nonfaulty n) (event : run.event time n = .resume_request request response) :
    ∃ later index, time ≤ later ∧ 1 ≤ index ∧ agreed later index (request, response) := by
  cases leader : run.leader time n with
  | false => exact former time n request response hn leader event
  | true => exact consensus.currentLeaderProgress time n request response hn leader event

/-- Lemma 3: admission and completion of the paper's request handler produce an
actual proposal. The two extra scheduling/consensus premises are explicit. -/
theorem lemma_3_eventual_agreement (consensus : Consensus run nonfaulty agreed)
    (handlers : RequestProgress run nonfaulty)
    {submitted : Request → Prop} (admission : LeaderAdmission run nonfaulty agreed submitted)
    (former : FormerLeaderProposalProgress run nonfaulty agreed)
    (request : Request) (submittedRequest : submitted request) :
    ∃ time index response, 1 ≤ index ∧ agreed time index (request, response) := by
  classical
  by_cases done : ∃ time index response, 1 ≤ index ∧ agreed time index (request, response)
  · exact done
  obtain ⟨time, n, payload, hn, leader, event⟩ := admission request submittedRequest done
  have issued := run.request_event_issued time n request payload leader event
  by_cases proposed : Requests.Proposed (run.state (time + 1) n).requests request
  · obtain ⟨⟨rid, response⟩, member, same⟩ := List.mem_map.mp proposed
    change rid = request at same
    subst rid
    obtain ⟨earlier, _, resume⟩ := run.proposal_origin (time + 1) n member
    obtain ⟨later, index, _, positive, committed⟩ :=
      proposal_event_eventually_agreed run consensus former earlier n request response hn resume
    exact ⟨later, index, response, positive, committed⟩
  · obtain ⟨resumeTime, response, _, resume⟩ := handlers.resume (time + 1) n request hn issued proposed
    obtain ⟨later, index, _, positive, committed⟩ :=
      proposal_event_eventually_agreed run consensus former resumeTime n request response hn resume
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
Unlike the paper's current statement, CG1 and the two extra contracts are visible
premises; see the assumption-gap report for their interpretation. -/
theorem theorem_2_liveness (consensus : Consensus run nonfaulty agreed)
    (handlers : RequestProgress run nonfaulty)
    {submitted : Request → Prop} (admission : LeaderAdmission run nonfaulty agreed submitted)
    (former : FormerLeaderProposalProgress run nonfaulty agreed) :
    ∀ request, submitted request → ∀ n, nonfaulty n →
      EventuallyFrom 0 (fun time => ∃ response,
        (request, response) ∈ (run.state time n).delivery.delivered) := by
  intro request submittedRequest n hn
  obtain ⟨agreedTime, index, response, positive, committed⟩ :=
    lemma_3_eventual_agreement run consensus handlers admission former request submittedRequest
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
