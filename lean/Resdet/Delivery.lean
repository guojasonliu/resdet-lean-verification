import Resdet.Dedup

/-!
Delivery adapters for the shared request-ID deduplication helper.
The core derives seen IDs from its output; the protocol stores them explicitly.
Both use `dedupFrom` to select new responses, preserving their input order.
-/
namespace Resdet

variable {Request Response : Type} [DecidableEq Request]

/-- Extend a delivery history with the first response for each unseen ID. -/
def applyItems (items output : List (Item Request Response)) : List (Item Request Response) :=
  output ++ dedupFrom (output.map Prod.fst) items

/-- Maintain the paper's delivery-deduplication state alongside the output history. -/
def applyWithDedup (items : List (Item Request Response)) (seen : List Request)
    (output : List (Item Request Response)) : List Request × List (Item Request Response) :=
  let fresh := dedupFrom seen items
  (seen ++ fresh.map Prod.fst, output ++ fresh)

/-- The explicit deduplication state agrees with the history-derived adapter. -/
theorem applyWithDedup_correct (items : List (Item Request Response)) (seen : List Request)
    (output : List (Item Request Response)) (consistent : seen = output.map Prod.fst) :
    applyWithDedup items seen output =
      ((applyItems items output).map Prod.fst, applyItems items output) := by
  subst seen
  simp [applyWithDedup, applyItems, List.map_append]

theorem dedup_eq_applyItems (items : List (Item Request Response)) :
    dedup items = applyItems items [] := by
  simp [applyItems, dedup]

/-- Processing consecutive batches is equivalent to processing their concatenation. -/
theorem applyItems_append (xs ys output : List (Item Request Response)) :
    applyItems (xs ++ ys) output = applyItems ys (applyItems xs output) := by
  simp [applyItems, dedupFrom_append, List.map_append, List.append_assoc]

theorem output_prefix_applyItems (items output : List (Item Request Response)) :
    output <+: applyItems items output :=
  List.prefix_append _ _

theorem applyItems_nodup (items output : List (Item Request Response))
    (unique : (output.map Prod.fst).Nodup) :
    ((applyItems items output).map Prod.fst).Nodup := by
  simp only [applyItems, List.map_append, List.nodup_append]
  refine ⟨unique, dedupFrom_nodup _ _, ?_⟩
  intro a ha b hb same
  obtain ⟨item, member, id⟩ := List.mem_map.mp hb
  have fresh := dedupFrom_fresh member
  exact fresh (by simpa [id, same] using ha)

theorem applyItems_mem {item : Item Request Response}
    (items output : List (Item Request Response))
    (member : item ∈ applyItems items output) : item ∈ output ∨ item ∈ items := by
  rcases List.mem_append.mp member with old | fresh
  · exact Or.inl old
  · exact Or.inr (dedupFrom_mem fresh)

/-- Every input ID is delivered, possibly using a response delivered earlier. -/
theorem applyItems_covers (items output : List (Item Request Response)) :
    ∀ request, request ∈ output.map Prod.fst ∨ request ∈ items.map Prod.fst →
      request ∈ (applyItems items output).map Prod.fst := by
  intro request member
  simp only [applyItems, List.map_append, List.mem_append]
  rcases member with old | incoming
  · exact Or.inl old
  · exact dedupFrom_covers _ _ request incoming

end Resdet
