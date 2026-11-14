import Resdet.HandlerProofs

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

/-- Lemmas 1 and 2 give the same ordered entries up to the shorter processed prefix. -/
theorem processed_history_prefix {left right : LocalState Request Response}
    (hl : LocalInvariant left) (hr : LocalInvariant right)
    (cg1 : IndexAgreement left right) (order : left.processed ≤ right.processed) :
    left.history <+: right.history := by
  apply List.prefix_iff_getElem?.mpr
  intro k inside
  have bound : k < left.processed := by rwa [hl.historyLength] at inside
  obtain ⟨a, lentry, _⟩ := lemma_2_no_hole_processing hl left.processed (Nat.le_refl _)
    (k + 1) (by omega) (by omega)
  obtain ⟨b, rentry, _⟩ := lemma_2_no_hole_processing hr left.processed order
    (k + 1) (by omega) (by omega)
  have same := lemma_1_same_processed_entry hl hr cg1 (by omega : 1 ≤ k + 1) lentry rentry
  simp only [Nat.add_sub_cancel] at lentry rentry
  have eq : a = left.history[k] :=
    Option.some.inj (lentry.symm.trans (List.getElem?_eq_getElem inside))
  simpa [← same, eq] using rentry

/-- Theorem 1: any two deliveries of one request ID have the same response. -/
theorem theorem_1_safety {left right : LocalState Request Response}
    (hl : LocalInvariant left) (hr : LocalInvariant right)
    (cg1 : IndexAgreement left right) {request : Request} {a b : Response}
    (ha : (request, a) ∈ left.delivered) (hb : (request, b) ∈ right.delivered) : a = b := by
  rw [hl.delivery] at ha
  rw [hr.delivery] at hb
  rcases Nat.le_total left.processed right.processed with order | order
  · have pre := dedup_prefix (processed_history_prefix hl hr cg1 order)
    exact congrArg Prod.snd (eq_of_same_id (dedup_nodup right.history) (pre.subset ha) hb rfl)
  · have reverse : IndexAgreement right left := fun i x y hi hx hy => (cg1 i y x hi hy hx).symm
    have pre := dedup_prefix (processed_history_prefix hr hl reverse order)
    exact congrArg Prod.snd (eq_of_same_id (dedup_nodup left.history) ha (pre.subset hb) rfl)

theorem at_most_once_delivery {s : LocalState Request Response} (h : LocalInvariant s) :
    (s.delivered.map Prod.fst).Nodup := by
  rw [h.delivery]
  exact dedup_nodup _

end Resdet
