import Resdet.consensus_assumptions

/-!
Section 5, safety. Delivery/log invariants are proved from the handlers here,
followed by Lemmas 1--2 and Theorem 1. The execution theorem requires CG1;
it has no leadership-retention or liveness premise.
-/

/-! ## Delivery deduplication facts -/
namespace Resdet

variable {Request Response : Type} [DecidableEq Request]

/-- The explicit deduplication state continues to match the delivery history. -/
theorem deliver_consistent (items : List (Item Request Response))
    (s : DeliveryState Request Response) (consistent : s.seen = s.delivered.map Prod.fst) :
    (deliver items s).seen = (deliver items s).delivered.map Prod.fst := by
  simp [deliver, consistent, List.map_append]

theorem deliver_empty (s : DeliveryState Request Response) : deliver [] s = s := by
  cases s
  simp [deliver, dedupFrom]

theorem deliver_initial (items : List (Item Request Response)) :
    (deliver items {}).delivered = dedup items := by
  simp [deliver, dedup]

/-- Processing consecutive batches equals processing their concatenation. -/
theorem deliver_append (xs ys : List (Item Request Response))
    (s : DeliveryState Request Response) :
    deliver (xs ++ ys) s = deliver ys (deliver xs s) := by
  simp [deliver, dedupFrom_append, List.map_append, List.append_assoc]

theorem delivered_prefix_deliver (items : List (Item Request Response))
    (s : DeliveryState Request Response) : s.delivered <+: (deliver items s).delivered :=
  List.prefix_append _ _

theorem deliver_nodup (items : List (Item Request Response))
    (s : DeliveryState Request Response) (consistent : s.seen = s.delivered.map Prod.fst)
    (unique : (s.delivered.map Prod.fst).Nodup) :
    ((deliver items s).delivered.map Prod.fst).Nodup := by
  simp only [deliver, consistent, List.map_append, List.nodup_append]
  refine ⟨unique, dedupFrom_nodup _ _, ?_⟩
  intro a ha b hb same
  obtain ⟨item, member, id⟩ := List.mem_map.mp hb
  have fresh := dedupFrom_fresh member
  exact fresh (by simpa [id, same] using ha)

theorem deliver_mem {item : Item Request Response}
    (items : List (Item Request Response)) (s : DeliveryState Request Response)
    (member : item ∈ (deliver items s).delivered) : item ∈ s.delivered ∨ item ∈ items := by
  rcases List.mem_append.mp member with old | fresh
  · exact Or.inl old
  · exact Or.inr (dedupFrom_mem fresh)

end Resdet

/-! ## Learning and processing preserve the safety invariant -/
namespace Resdet

variable {Request Response : Type} [DecidableEq Request]

/-- Proved from the handlers; none of these facts is a transition guard. -/
structure LocalInvariant (s : LocalState Request Response) : Prop where
  processedBound : s.processed ≤ s.learned
  logBound : ∀ k entry, s.log k = some entry → k ≤ s.learned
  historyLength : s.history.length = s.processed
  historyLog : ∀ k, k < s.processed → s.history[k]? = s.log (k + 1)
  consistent : s.seen = s.delivered.map Prod.fst
  delivery : s.delivered = dedup s.history

theorem initialLocal_invariant : LocalInvariant (initialLocal : LocalState Request Response) := by
  constructor <;> simp [initialLocal, dedup, dedupFrom]

theorem processEntry_invariant {s : LocalState Request Response}
    (h : LocalInvariant s) {entry : Item Request Response}
    (next : s.processed + 1 ≤ s.learned)
    (recorded : s.log (s.processed + 1) = some entry) :
    LocalInvariant (processEntry s entry) := by
  constructor
  · exact next
  · exact h.logBound
  · simp [processEntry, h.historyLength]
  · intro k hk
    by_cases old : k < s.processed
    · simpa [processEntry, List.getElem?_append_left, h.historyLength, old] using h.historyLog k old
    · have eq : k = s.processed := by simp only [processEntry] at hk; omega
      subst k
      change (s.history ++ [entry])[s.processed]? = s.log (s.processed + 1)
      rw [List.getElem?_append_right (Nat.le_of_eq h.historyLength), h.historyLength, Nat.sub_self]
      exact recorded.symm
  · exact deliver_consistent [entry] s.toDeliveryState h.consistent
  · simp only [processEntry, deliver]
    rw [h.consistent, h.delivery]
    simp [dedup, dedupFrom_append]

theorem processLoop_invariant (fuel : Nat) {s : LocalState Request Response}
    (h : LocalInvariant s) : LocalInvariant (processLoop fuel s) := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
      simp only [processLoop]
      split
      next next =>
        split
        next => exact h
        next entry recorded => exact ih (processEntry_invariant h next recorded)
      next => exact h

theorem process_invariant {s : LocalState Request Response} (h : LocalInvariant s) :
    LocalInvariant (process s) := processLoop_invariant _ h

theorem recordLearn_invariant {s : LocalState Request Response} (h : LocalInvariant s)
    (index : Nat) (entry : Item Request Response) (fresh : s.log index = none) :
    LocalInvariant (recordLearn s index entry) := by
  constructor
  · exact Nat.le_trans h.processedBound (Nat.le_max_left _ _)
  · intro k value recorded
    by_cases same : k = index
    · subst k; exact Nat.le_max_right _ _
    · exact Nat.le_trans (h.logBound k value (by simpa [recordLearn, same] using recorded))
        (Nat.le_max_left _ _)
  · exact h.historyLength
  · intro k hk
    change k < s.processed at hk
    have unequal : k + 1 ≠ index := by
      intro eq
      have inHistory : s.history[k]? ≠ none := by
        intro missing
        have bound := List.getElem?_eq_none_iff.mp missing
        have length := h.historyLength
        omega
      rw [h.historyLog k hk, eq, fresh] at inHistory
      exact inHistory rfl
    simpa [recordLearn, unequal] using h.historyLog k hk
  · exact h.consistent
  · exact h.delivery

theorem handle_learn_invariant {s : LocalState Request Response} (h : LocalInvariant s)
    (index : Nat) (entry : Item Request Response) :
    LocalInvariant (handle_learn s index entry) := by
  unfold handle_learn
  split
  next => exact h
  next fresh => exact process_invariant (recordLearn_invariant h index entry fresh)

theorem processLoop_log (fuel : Nat) (s : LocalState Request Response) :
    (processLoop fuel s).log = s.log := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      simp only [processLoop]
      split
      · split
        · rfl
        · exact ih _
      · rfl

theorem process_log (s : LocalState Request Response) : (process s).log = s.log :=
  processLoop_log _ _

theorem processLoop_history_prefix (fuel : Nat) (s : LocalState Request Response) :
    s.history <+: (processLoop fuel s).history := by
  induction fuel generalizing s with
  | zero => exact List.prefix_refl _
  | succ fuel ih =>
      simp only [processLoop]
      split
      · split
        · exact List.prefix_refl _
        next entry _ =>
          exact (List.prefix_append s.history [entry]).trans (ih (processEntry s entry))
      · exact List.prefix_refl _

theorem handle_learn_history_prefix (s : LocalState Request Response)
    (index : Nat) (entry : Item Request Response) :
    s.history <+: (handle_learn s index entry).history := by
  unfold handle_learn
  split
  · exact List.prefix_refl _
  · exact processLoop_history_prefix _ (recordLearn s index entry)

/-- Previously recorded local entries cannot be overwritten. -/
theorem handle_learn_log_preserved (s : LocalState Request Response)
    (index : Nat) (entry : Item Request Response) {k : Nat} {old : Item Request Response}
    (present : s.log k = some old) : (handle_learn s index entry).log k = some old := by
  unfold handle_learn
  split
  · exact present
  next fresh =>
    rw [process_log]
    have unequal : k ≠ index := by intro eq; subst k; simp [fresh] at present
    simpa [recordLearn, unequal] using present

/-- A stored entry came from this callback or was already in the local log. -/
theorem handle_learn_log_origin (s : LocalState Request Response)
    (index : Nat) (entry : Item Request Response) {k : Nat} {value : Item Request Response}
    (present : (handle_learn s index entry).log k = some value) :
    s.log k = some value ∨ k = index ∧ value = entry := by
  unfold handle_learn at present
  split at present
  · exact Or.inl present
  next fresh =>
    rw [process_log] at present
    by_cases same : k = index
    · exact Or.inr ⟨same, (Option.some.inj (by simpa [recordLearn, same] using present)).symm⟩
    · exact Or.inl (by simpa [recordLearn, same] using present)

theorem processLoop_delivery_prefix (fuel : Nat) (s : LocalState Request Response) :
    s.delivered <+: (processLoop fuel s).delivered := by
  induction fuel generalizing s with
  | zero => exact List.prefix_refl _
  | succ fuel ih =>
      simp only [processLoop]
      split
      · split
        · exact List.prefix_refl _
        next entry _ =>
          exact (delivered_prefix_deliver [entry] s.toDeliveryState).trans
            (ih (processEntry s entry))
      · exact List.prefix_refl _

theorem handle_learn_delivery_prefix (s : LocalState Request Response)
    (index : Nat) (entry : Item Request Response) :
    s.delivered <+: (handle_learn s index entry).delivered := by
  unfold handle_learn
  split
  · exact List.prefix_refl _
  · exact processLoop_delivery_prefix _ (recordLearn s index entry)

end Resdet

/-! ## Induction over execution time -/
namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]

theorem propagate {p : Nat → Prop} (next : ∀ t, p t → p (t + 1))
    {a b : Nat} (order : a ≤ b) (ha : p a) : p b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le order
  clear order
  induction d with
  | zero => simpa using ha
  | succ d ih => exact next _ ih

end Resdet

/-! ## One step preserves safety and recorded history -/
namespace Resdet.Step

variable {Node Request Payload Response : Type} [DecidableEq Request]

theorem invariant {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t)
    (hs : LocalInvariant s.delivery) : LocalInvariant t.delivery := by
  cases h with
  | handle_learn => exact handle_learn_invariant hs _ _
  | _ => exact hs

theorem log_preserved {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t)
    {index : Nat} {entry : Item Request Response} (recorded : s.delivery.log index = some entry) :
    t.delivery.log index = some entry := by
  cases h with
  | handle_learn => exact handle_learn_log_preserved _ _ _ recorded
  | _ => exact recorded

theorem log_origin {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t)
    {index : Nat} {entry : Item Request Response} (recorded : t.delivery.log index = some entry) :
    s.delivery.log index = some entry ∨
      ∃ receivedAt, event = .handle_learn receivedAt index entry := by
  cases h with
  | handle_learn =>
      rcases handle_learn_log_origin _ _ _ recorded with old | ⟨rfl, rfl⟩
      · exact Or.inl old
      · exact Or.inr ⟨_, rfl⟩
  | _ => exact Or.inl recorded

theorem delivery_prefix {leader : Bool} {event : Event Request Payload Response}
    {s t : Replica Request Payload Response} (h : Step leader event s t) :
    s.delivery.delivered <+: t.delivery.delivered := by
  cases h with
  | handle_learn => exact handle_learn_delivery_prefix _ _ _
  | _ => exact List.prefix_refl _

end Resdet.Step

/-! ## Safety and history throughout an execution -/
namespace Resdet.Execution

variable {Node Request Payload Response : Type} [DecidableEq Request]
variable (run : Execution Node Request Payload Response)

theorem invariant (time : Nat) (n : Node) : LocalInvariant (run.state time n).delivery := by
  induction time with
  | zero => simpa [run.initial] using (initialLocal_invariant (Request := Request) (Response := Response))
  | succ time ih => exact (run.next time n).invariant ih

theorem log_mono (n : Node) {a b index : Nat} {entry : Item Request Response}
    (order : a ≤ b) (recorded : (run.state a n).delivery.log index = some entry) :
    (run.state b n).delivery.log index = some entry :=
  propagate (fun time present => (run.next time n).log_preserved present) order recorded

theorem log_origin (time : Nat) (n : Node) {index : Nat} {entry : Item Request Response}
    (recorded : (run.state time n).delivery.log index = some entry) :
    ∃ earlier receivedAt, earlier < time ∧
      run.event earlier n = .handle_learn receivedAt index entry := by
  induction time with
  | zero => simp [run.initial, initialLocal] at recorded
  | succ time ih =>
      rcases (run.next time n).log_origin recorded with old | ⟨receivedAt, event⟩
      · obtain ⟨earlier, receipt, before, origin⟩ := ih old
        exact ⟨earlier, receipt, by omega, origin⟩
      · exact ⟨time, receivedAt, Nat.lt_succ_self _, event⟩

theorem delivery_mono (n : Node) {a b : Nat} (order : a ≤ b) :
    (run.state a n).delivery.delivered <+: (run.state b n).delivery.delivered :=
  propagate (p := fun time => (run.state a n).delivery.delivered <+:
    (run.state time n).delivery.delivered)
    (fun time pre => pre.trans (run.next time n).delivery_prefix) order (List.prefix_refl _)

end Resdet.Execution

/-! ## Lemmas 1--2 and Theorem 1 -/
namespace Resdet

variable {Request Response : Type} [DecidableEq Request]

/-- CG1 for independently recorded local logs; it may compare different times. -/
def IndexAgreement (left right : LocalState Request Response) : Prop :=
  ∀ index a b, 1 ≤ index → left.log index = some a → right.log index = some b → a = b

/-- Lemma 1: the same processed index contains the same entry, by CG1. -/
theorem lemma_1_same_processed_entry {left right : LocalState Request Response}
    (hl : LocalInvariant left) (hr : LocalInvariant right)
    (cg1 : IndexAgreement left right) {index : Nat} (positive : 1 ≤ index)
    {a b : Item Request Response}
    (pl : left.history[index - 1]? = some a)
    (pr : right.history[index - 1]? = some b) : a = b := by
  have il : index - 1 < left.processed := by
    rw [← hl.historyLength]
    exact (List.getElem?_eq_some_iff.mp pl).1
  have ir : index - 1 < right.processed := by
    rw [← hr.historyLength]
    exact (List.getElem?_eq_some_iff.mp pr).1
  have llog : left.log index = some a := by
    simpa only [Nat.sub_add_cancel positive] using (hl.historyLog (index - 1) il).symm.trans pl
  have rlog : right.log index = some b := by
    simpa only [Nat.sub_add_cancel positive] using (hr.historyLog (index - 1) ir).symm.trans pr
  exact cg1 index a b positive llog rlog

/-- Lemma 2: processing index i includes every positive index through i. -/
theorem lemma_2_no_hole_processing {s : LocalState Request Response}
    (h : LocalInvariant s) (index : Nat) (processed : index ≤ s.processed) :
    ∀ earlier, 1 ≤ earlier → earlier ≤ index →
      ∃ entry, s.history[earlier - 1]? = some entry ∧ s.log earlier = some entry := by
  intro earlier positive before
  have inside : earlier - 1 < s.history.length := by rw [h.historyLength]; omega
  refine ⟨s.history[earlier - 1], List.getElem?_eq_getElem inside, ?_⟩
  simpa only [Nat.sub_add_cancel positive] using
    (h.historyLog (earlier - 1) (by omega)).symm.trans (List.getElem?_eq_getElem inside)

/-- The first processed log entry for this request, using the paper's one-based indices. -/
private structure FirstOccurrence (s : LocalState Request Response) (request : Request)
    (response : Response) (index : Nat) : Prop where
  positive : 1 ≤ index
  processed : index ≤ s.processed
  entry : s.history[index - 1]? = some (request, response)
  first : ∀ k, 1 ≤ k → k < index → ∀ y, s.history[k - 1]? ≠ some (request, y)

/-- Delivery deduplication keeps the response at the first processed index for its ID. -/
private theorem delivered_at_first_index {s : LocalState Request Response} (inv : LocalInvariant s)
    {request : Request} {response : Response} (delivered : (request, response) ∈ s.delivered) :
    ∃ i, FirstOccurrence s request response i := by
  rw [inv.delivery] at delivered
  obtain ⟨k, found, first⟩ := dedupFrom_first_occurrence delivered
  have inside := (List.getElem?_eq_some_iff.mp found).1
  rw [inv.historyLength] at inside
  refine ⟨k + 1, by omega, by omega, found, ?_⟩
  intro j positive earlier
  exact first (j - 1) (by omega)

/-- If the other replica delivered later, it had already processed this ID at i. -/
private theorem FirstOccurrence.not_before {r t : LocalState Request Response}
    (hr : LocalInvariant r) (ht : LocalInvariant t) (cg1 : IndexAgreement r t)
    {request : Request} {a b : Response} {i j : Nat}
    (atR : FirstOccurrence r request a i) (atT : FirstOccurrence t request b j) : ¬ i < j := by
  intro earlier
  obtain ⟨entry, atEarlier, _⟩ :=
    lemma_2_no_hole_processing ht j atT.processed i atR.positive (Nat.le_of_lt earlier)
  have same := lemma_1_same_processed_entry hr ht cg1 atR.positive atR.entry atEarlier
  rw [← same] at atEarlier
  exact atT.first i atR.positive earlier a atEarlier

/-- Theorem 1: any two deliveries of one request ID have the same response. -/
theorem theorem_1_safety {left right : LocalState Request Response}
    (hl : LocalInvariant left) (hr : LocalInvariant right)
    (cg1 : IndexAgreement left right) {request : Request} {a b : Response}
    (ha : (request, a) ∈ left.delivered) (hb : (request, b) ∈ right.delivered) : a = b := by
  obtain ⟨i, atLeft⟩ := delivered_at_first_index hl ha
  obtain ⟨j, atRight⟩ := delivered_at_first_index hr hb
  by_cases same : i = j
  · subst j
    have sameEntry := lemma_1_same_processed_entry hl hr cg1 atLeft.positive atLeft.entry atRight.entry
    exact congrArg Prod.snd sameEntry
  rcases Nat.lt_or_gt_of_ne same with earlier | later
  · exact False.elim (atLeft.not_before hl hr cg1 atRight earlier)
  · have reverse : IndexAgreement right left :=
      fun k x y positive hx hy => (cg1 k y x positive hy hx).symm
    exact False.elim (atRight.not_before hr hl reverse atLeft later)

theorem at_most_once_delivery {s : LocalState Request Response} (h : LocalInvariant s) :
    (s.delivered.map Prod.fst).Nodup := by
  rw [h.delivery]
  exact dedup_nodup _

end Resdet

/-! ## Theorem 1 on executions of the pseudocode -/
namespace Resdet

variable {Node Request Payload Response : Type} [DecidableEq Request]

/-- Theorem 1 on actual executions; local invariants are proved from the handlers. -/
theorem theorem_1_on_execution (run : Execution Node Request Payload Response)
    {nonfaulty : Node → Prop}
    (cg1 : CG1 run nonfaulty) (a b : Nat) (r t : Node)
    (hr : nonfaulty r) (ht : nonfaulty t) {request : Request} {left right : Response}
    (hl : (request, left) ∈ (run.state a r).delivery.delivered)
    (hr' : (request, right) ∈ (run.state b t).delivery.delivered) : left = right :=
  theorem_1_safety (run.invariant a r) (run.invariant b t)
    (fun index x y => cg1 a b r t index x y hr ht) hl hr'

end Resdet
