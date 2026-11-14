import Resdet.Protocol

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

theorem handle_learn_records (s : LocalState Request Response)
    (index : Nat) (entry : Item Request Response) (fresh : s.log index = none) :
    (handle_learn s index entry).log index = some entry := by
  simp [handle_learn, fresh, process_log, recordLearn]

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

def PrefixPresent (s : LocalState Request Response) (target : Nat) : Prop :=
  ∀ k, 1 ≤ k → k ≤ target → ∃ entry, s.log k = some entry

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
