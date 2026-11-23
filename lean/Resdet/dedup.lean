import Std

/-!
Shared request-ID deduplication. A scan keeps the first item for each ID not
already seen. The delivery handlers use this helper and the guarantees below;
response values are arbitrary and only request IDs need decidable equality.
-/
namespace Resdet

abbrev Item (Request Response : Type) := Request × Response

variable {Request Response : Type} [DecidableEq Request]

/-- Keep the first occurrence of each ID absent from the supplied seen IDs. -/
def dedupFrom (seen : List Request) : List (Item Request Response) →
    List (Item Request Response)
  | [] => []
  | item :: rest =>
      if item.1 ∈ seen then dedupFrom seen rest
      else item :: dedupFrom (seen ++ [item.1]) rest

def dedup (items : List (Item Request Response)) := dedupFrom [] items

/-- Returned items always have IDs absent from the initial seen state. -/
theorem dedupFrom_fresh {seen : List Request} {items : List (Item Request Response)}
    {item : Item Request Response} (member : item ∈ dedupFrom seen items) :
    item.1 ∉ seen := by
  induction items generalizing seen with
  | nil => simp [dedupFrom] at member
  | cons head rest ih =>
      by_cases old : head.1 ∈ seen
      · exact ih (by simpa [dedupFrom, old] using member)
      · simp only [dedupFrom, if_neg old, List.mem_cons] at member
        rcases member with rfl | member
        · exact old
        · have fresh := ih member
          exact fun h => fresh (List.mem_append_left _ h)

/-- The returned IDs are unique, even if the input or seen list has duplicates. -/
theorem dedupFrom_nodup (seen : List Request) (items : List (Item Request Response)) :
    ((dedupFrom seen items).map Prod.fst).Nodup := by
  induction items generalizing seen with
  | nil => simp [dedupFrom]
  | cons item rest ih =>
      by_cases old : item.1 ∈ seen
      · simpa [dedupFrom, old] using ih seen
      · simp only [dedupFrom, if_neg old, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih _⟩
        intro member
        obtain ⟨next, inside, same⟩ := List.mem_map.mp member
        exact dedupFrom_fresh inside (by simp [same])

/-- Deduplication never invents an item or changes its response. -/
theorem dedupFrom_mem {seen : List Request} {items : List (Item Request Response)}
    {item : Item Request Response} (member : item ∈ dedupFrom seen items) :
    item ∈ items := by
  induction items generalizing seen with
  | nil => simp [dedupFrom] at member
  | cons head rest ih =>
      by_cases old : head.1 ∈ seen
      · exact List.mem_cons_of_mem _ (ih (by simpa [dedupFrom, old] using member))
      · simp only [dedupFrom, if_neg old, List.mem_cons] at member
        exact member.elim (fun eq => List.mem_cons.mpr (Or.inl eq))
          (fun h => List.mem_cons_of_mem _ (ih h))

/-- Every input ID is already seen or represented in the output. -/
theorem dedupFrom_covers (seen : List Request) (items : List (Item Request Response)) :
    ∀ request, request ∈ items.map Prod.fst →
      request ∈ seen ∨ request ∈ (dedupFrom seen items).map Prod.fst := by
  induction items generalizing seen with
  | nil => simp
  | cons item rest ih =>
      intro request member
      simp only [List.map_cons, List.mem_cons] at member
      by_cases old : item.1 ∈ seen
      · simp only [dedupFrom, if_pos old]
        rcases member with rfl | member
        · exact Or.inl old
        · exact ih seen request member
      · simp only [dedupFrom, if_neg old, List.map_cons, List.mem_cons]
        rcases member with rfl | member
        · exact Or.inr (Or.inl rfl)
        · rcases ih (seen ++ [item.1]) request member with earlier | later
          · simp only [List.mem_append, List.mem_singleton] at earlier
            exact earlier.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))
          · exact Or.inr (Or.inr later)

/-- Processing adjacent chunks equals one scan, carrying forward the new IDs. -/
theorem dedupFrom_append (seen : List Request) (xs ys : List (Item Request Response)) :
    dedupFrom seen (xs ++ ys) = dedupFrom seen xs ++
      dedupFrom (seen ++ (dedupFrom seen xs).map Prod.fst) ys := by
  induction xs generalizing seen with
  | nil => simp [dedupFrom]
  | cons item rest ih =>
      by_cases old : item.1 ∈ seen
      · simpa [dedupFrom, old] using ih seen
      · simp only [List.cons_append, dedupFrom, if_neg old]
        rw [ih]
        simp [List.map_cons, List.append_assoc]

theorem dedup_prefix {xs ys : List (Item Request Response)} (h : xs <+: ys) :
    dedup xs <+: dedup ys := by
  obtain ⟨suffix, rfl⟩ := h
  unfold dedup
  rw [dedupFrom_append]
  exact List.prefix_append _ _

theorem dedup_nodup (items : List (Item Request Response)) :
    ((dedup items).map Prod.fst).Nodup := dedupFrom_nodup [] items

theorem dedup_mem {item : Item Request Response} {items : List (Item Request Response)}
    (h : item ∈ dedup items) : item ∈ items := dedupFrom_mem h

theorem dedup_covers {items : List (Item Request Response)} {request : Request}
    (h : request ∈ items.map Prod.fst) : request ∈ (dedup items).map Prod.fst := by
  simpa using dedupFrom_covers [] items request h

omit [DecidableEq Request] in
/-- Within an ID-unique history, equal IDs identify the same response item. -/
theorem eq_of_same_id {items : List (Item Request Response)}
    (unique : (items.map Prod.fst).Nodup)
    {a b : Item Request Response} (ha : a ∈ items) (hb : b ∈ items)
    (ids : a.1 = b.1) : a = b := by
  induction items with
  | nil => simp at ha
  | cons first rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · rfl
        · exact False.elim (unique.1 (ids ▸ List.mem_map_of_mem hb))
      · rcases hb with rfl | hb
        · exact False.elim (unique.1 (ids ▸ List.mem_map_of_mem ha))
        · exact ih unique.2 ha hb

end Resdet
