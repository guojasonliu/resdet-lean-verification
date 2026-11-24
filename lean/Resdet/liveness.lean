import Resdet.safety
import Resdet.liveness_assumptions

/-! Section 5.3, Lemmas 3–5 and Theorem 2. -/
namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]

/-- A handler that passes the leader check starts its own RPC. -/
theorem Step.accepted_rpc_pending {s t : Replica Request Payload Response}
    {request : Request} {payload : Payload} (step : Step true (.handle_request request payload) s t) :
    (s.requests.calls.length, request) ∈ t.requests.pending := by
  cases step
  exact List.mem_cons_self

variable (run : Execution Node Request Payload Response)
variable {nonfaulty : Node → Prop} {agreed : Nat → Nat → Item Request Response → Prop}

/-- Lemma 3. In the absence of agreement, each retry starts an RPC (L1) and
eventually proposes a response (L3/L4). CG3(2) then gives agreement for this ID. -/
theorem lemma_3_eventual_agreement (consensus : Consensus run nonfaulty agreed)
    {submitted : Request → Prop} (liveness : LivenessAssumptions run nonfaulty agreed submitted)
    (request : Request) (submittedRequest : submitted request) :
    ∃ time index response, 1 ≤ index ∧ agreed time index (request, response) := by
  apply Classical.byContradiction
  intro neverAgreed
  have repeated : RepeatedProposals run request := by
    intro cutoff
    obtain ⟨time, n, payload, afterCutoff, healthy, leader, accepted⟩ :=
      liveness.requestAccepted cutoff request submittedRequest neverAgreed
    have step := run.next time n
    rw [leader, accepted] at step
    obtain ⟨later, response, afterCall, resumed⟩ :=
      liveness.rpcCompletes (time + 1) n _ request healthy step.accepted_rpc_pending
    exact ⟨later, n, _, response, by omega, resumed⟩
  obtain ⟨_, _, _, response, time, index, _, _, positive, agreedEntry⟩ :=
    consensus.repeatedProposalProgress request repeated
  exact neverAgreed ⟨time, index, response, positive, agreedEntry⟩

end Resdet

/-! ## Learn callbacks record their entries -/
namespace Resdet

variable {Request Response : Type} [DecidableEq Request]

theorem handle_learn_records (s : LocalState Request Response)
    (index : Nat) (entry : Item Request Response) (fresh : s.log index = none) :
    (handle_learn s index entry).log index = some entry := by
  simp [handle_learn, fresh, process_log, recordLearn]

end Resdet

/-! ## The learn step runs the callback -/
namespace Resdet.Step

variable {Node Request Payload Response : Type} [DecidableEq Request]

theorem learn_result {s t : Replica Request Payload Response}
    {leader : Bool} {index : Nat} {entry : Item Request Response}
    (h : Step leader (.handle_learn index entry) s t) :
    t.delivery = Resdet.handle_learn s.delivery index entry := by
  cases h
  rfl

end Resdet.Step

/-! ## Repeated callbacks agree with existing entries -/
namespace Resdet.Execution

variable {Node Request Payload Response : Type} [DecidableEq Request]
variable (run : Execution Node Request Payload Response)
variable {nonfaulty : Node → Prop} {agreed : Nat → Nat → Item Request Response → Prop}

/-- When the slot is already present, the earlier callback carried the unique
committed entry at this index (Section 4.1). -/
theorem learn_event_recorded (consensus : Consensus run nonfaulty agreed)
    {agreedAt : Nat}
    (time : Nat) (n : Node) (hn : nonfaulty n) (index : Nat) (entry : Item Request Response)
    (positive : 1 ≤ index) (committed : agreed agreedAt index entry)
    (event : run.event time n = .handle_learn index entry) :
    (run.state (time + 1) n).delivery.log index = some entry := by
  have step := run.next time n
  rw [event] at step
  rw [step.learn_result]
  cases recorded : (run.state time n).delivery.log index with
  | none => exact handle_learn_records _ _ _ recorded
  | some old =>
      obtain ⟨earlier, _, callback⟩ := run.log_origin time n recorded
      obtain ⟨oldTime, _, oldCommitted⟩ :=
        consensus.callbackOrigin earlier n index old hn positive callback
      have same := consensus.agreedEntryUnique oldTime agreedAt index old entry
        positive oldCommitted committed
      simp [handle_learn, recorded, same]

end Resdet.Execution

/-! ## Present local prefixes -/
namespace Resdet

variable {Request Response : Type} [DecidableEq Request]

def PrefixPresent (s : LocalState Request Response) (target : Nat) : Prop :=
  ∀ k, 1 ≤ k → k ≤ target → ∃ entry, s.log k = some entry

end Resdet

/-! ## Lemma 4: eventual prefix learning -/
namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]
variable (run : Execution Node Request Payload Response)
variable {nonfaulty : Node → Prop} {agreed : Nat → Nat → Item Request Response → Prop}

/-- CG3(3) and L4 ensure that the replica eventually has the agreed entry,
including when its callback finds the entry already recorded. -/
theorem agreed_eventually_recorded (consensus : Consensus run nonfaulty agreed)
    (start index : Nat) (entry : Item Request Response) (positive : 1 ≤ index)
    (committed : agreed start index entry) (n : Node) (hn : nonfaulty n) :
    EventuallyFrom start (fun time => (run.state time n).delivery.log index = some entry) := by
  rcases consensus.learnCallbacks start index entry positive committed n hn with old | later
  · exact ⟨start, Nat.le_refl _, old⟩
  · obtain ⟨time, afterStart, event⟩ := later
    exact ⟨time + 1, by omega,
      run.learn_event_recorded consensus time n hn index entry positive committed event⟩

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

end Resdet

/-! ## The processing loop drains an available prefix -/
namespace Resdet

variable {Request Response : Type} [DecidableEq Request]

/-- Enough fuel and a complete next prefix make the loop reach its last slot. -/
theorem processLoop_reaches (fuel : Nat) (s : LocalState Request Response) (target : Nat)
    (watermark : target ≤ s.learned) (enough : target ≤ s.processed + fuel)
    (present : ∀ k, s.processed < k → k ≤ target → ∃ entry, s.log k = some entry) :
    target ≤ (processLoop fuel s).processed := by
  induction fuel generalizing s with
  | zero => simpa [processLoop] using enough
  | succ fuel ih =>
      by_cases finished : target ≤ s.processed
      · simp only [processLoop]
        split
        · split
          · exact finished
          next entry _ =>
            exact ih (processEntry s entry) watermark (by simp [processEntry]; omega)
              (by intro k hk ht; exact present k (by simp [processEntry] at hk; omega) ht)
        · exact finished
      · have next : s.processed + 1 ≤ s.learned := by omega
        obtain ⟨entry, recorded⟩ := present (s.processed + 1) (by omega) (by omega)
        simp only [processLoop, if_pos next, recorded]
        exact ih (processEntry s entry) watermark (by simp [processEntry]; omega)
          (by intro k hk ht; exact present k (by simp [processEntry] at hk; omega) ht)

theorem process_reaches (s : LocalState Request Response) (target : Nat)
    (watermark : target ≤ s.learned)
    (present : ∀ k, s.processed < k → k ≤ target → ∃ entry, s.log k = some entry) :
    target ≤ (process s).processed := by
  apply processLoop_reaches _ s target watermark
  · omega
  · exact present

/-- A completed callback has drained every available contiguous prefix. -/
def Completed (s : LocalState Request Response) : Prop :=
  ∀ target, PrefixPresent s target → target ≤ s.processed

omit [DecidableEq Request] in
theorem initialLocal_completed : Completed (initialLocal : LocalState Request Response) := by
  intro target present
  by_cases zero : target = 0
  · simp [zero, initialLocal]
  · obtain ⟨entry, recorded⟩ := present 1 (by omega) (by omega)
    simp [initialLocal] at recorded

theorem handle_learn_completed {s : LocalState Request Response}
    (h : LocalInvariant s) (complete : Completed s)
    (index : Nat) (entry : Item Request Response) :
    Completed (handle_learn s index entry) := by
  unfold handle_learn
  split
  · exact complete
  next fresh =>
    intro target present
    have presentPrefix : PrefixPresent (recordLearn s index entry) target := by
      simpa only [PrefixPresent, process_log] using present
    have watermark : target ≤ (recordLearn s index entry).learned := by
      by_cases zero : target = 0
      · omega
      · obtain ⟨value, recorded⟩ := presentPrefix target (by omega) (Nat.le_refl _)
        exact (recordLearn_invariant h index entry fresh).logBound target value recorded
    exact process_reaches _ target watermark
      (fun k lower upper => presentPrefix k (by omega) upper)

end Resdet

/-! ## A learn step completes processing -/
namespace Resdet.Step

variable {Node Request Payload Response : Type} [DecidableEq Request]

theorem completed {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t)
    (hs : LocalInvariant s.delivery) (hc : Completed s.delivery) : Completed t.delivery := by
  cases h with
  | handle_learn => exact handle_learn_completed hs hc _ _
  | _ => exact hc

end Resdet.Step

/-! ## Completed processing throughout an execution -/
namespace Resdet.Execution

variable {Node Request Payload Response : Type} [DecidableEq Request]
variable (run : Execution Node Request Payload Response)

theorem completed (time : Nat) (n : Node) : Completed (run.state time n).delivery := by
  induction time with
  | zero => simpa [run.initial] using (initialLocal_completed (Request := Request) (Response := Response))
  | succ time ih => exact (run.next time n).completed (run.invariant time n) ih

end Resdet.Execution

/-! ## Lemma 5: processing covers each request ID -/
namespace Resdet

variable {Request Response : Type} [DecidableEq Request]

/-- Every input ID is represented afterward, possibly by an earlier response. -/
theorem deliver_covers (items : List (Item Request Response))
    (s : DeliveryState Request Response) (consistent : s.seen = s.delivered.map Prod.fst) :
    ∀ request, request ∈ s.delivered.map Prod.fst ∨ request ∈ items.map Prod.fst →
      request ∈ (deliver items s).delivered.map Prod.fst := by
  intro request member
  simp only [deliver, List.map_append, List.mem_append]
  rcases member with old | incoming
  · exact Or.inl old
  · simpa [consistent] using dedupFrom_covers s.seen items request incoming

/-- Once a prefix is processed, every ID in it is represented in delivery. -/
theorem processed_entry_delivered {s : LocalState Request Response} (h : LocalInvariant s)
    {index : Nat} {entry : Item Request Response} (positive : 1 ≤ index)
    (processed : index ≤ s.processed) (recorded : s.log index = some entry) :
    ∃ response, (entry.1, response) ∈ s.delivered := by
  have inHistory : s.history[index - 1]? = some entry := by
    rw [h.historyLog (index - 1) (by omega), Nat.sub_add_cancel positive]
    exact recorded
  have member : entry ∈ s.history := List.mem_of_getElem? inHistory
  have covered := dedup_covers (List.mem_map_of_mem member)
  rw [← h.delivery] at covered
  obtain ⟨item, inside, same⟩ := List.mem_map.mp covered
  rcases item with ⟨id, value⟩
  simp only at same
  subst id
  exact ⟨value, inside⟩

/-- Paper Lemma 5 at a completed handler boundary. -/
theorem lemma_5_eventual_delivery {s : LocalState Request Response}
    (h : LocalInvariant s) (complete : Completed s) {index : Nat}
    {entry : Item Request Response} (positive : 1 ≤ index)
    (presentPrefix : PrefixPresent s index) (recorded : s.log index = some entry) :
    ∃ response, (entry.1, response) ∈ s.delivered :=
  processed_entry_delivered h positive (complete index presentPrefix) recorded

end Resdet

/-! ## Lemma 5 on executions and Theorem 2 -/
namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]
variable (run : Execution Node Request Payload Response)
variable {nonfaulty : Node → Prop} {agreed : Nat → Nat → Item Request Response → Prop}

/-- Lemma 5 on executions: `handle_learn` already completed its `process` loop,
so a present contiguous prefix has already produced a response for this ID. -/
theorem lemma_5_on_execution (time : Nat) (n : Node) (index : Nat)
    (entry : Item Request Response) (positive : 1 ≤ index)
    (prefixPresent : PrefixPresent (run.state time n).delivery index)
    (recorded : (run.state time n).delivery.log index = some entry) :
    ∃ response, (entry.1, response) ∈ (run.state time n).delivery.delivered :=
  lemma_5_eventual_delivery (run.invariant time n) (run.completed time n) positive prefixPresent recorded

/-- Theorem 2: the three numbered liveness lemmas compose into eventual delivery.
Each learned slot retains the committed entry supplied by the consensus callback. -/
theorem theorem_2_liveness (consensus : Consensus run nonfaulty agreed)
    {submitted : Request → Prop} (liveness : LivenessAssumptions run nonfaulty agreed submitted) :
    ∀ request, submitted request → ∀ n, nonfaulty n →
      EventuallyFrom 0 (fun time => ∃ response,
        (request, response) ∈ (run.state time n).delivery.delivered) := by
  intro request submittedRequest n hn
  obtain ⟨agreedTime, index, response, positive, committed⟩ :=
    lemma_3_eventual_agreement run consensus liveness request submittedRequest
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
