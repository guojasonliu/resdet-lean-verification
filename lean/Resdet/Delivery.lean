import Resdet.Dedup

/-!
One delivery operation for both the delivery model and the request protocol.
The stored request IDs and observable output are updated together.
-/
namespace Resdet

structure DeliveryState (Request Response : Type) where
  seen : List Request := []
  delivered : List (Item Request Response) := []
  deriving DecidableEq

variable {Request Response : Type} [DecidableEq Request]

/-- Deliver the first response for each unseen ID, preserving item order. -/
def deliver (items : List (Item Request Response)) (s : DeliveryState Request Response) :
    DeliveryState Request Response :=
  let fresh := dedupFrom s.seen items
  { seen := s.seen ++ fresh.map Prod.fst, delivered := s.delivered ++ fresh }

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

end Resdet
