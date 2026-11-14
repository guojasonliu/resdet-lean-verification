import Resdet.Protocol

namespace Resdet.Protocol

variable {Node Request Payload Response : Type}
variable [DecidableEq Node] [DecidableEq Request]
variable {cfg : Config} {leader : Node} {s t : State Node Request Payload Response}

theorem step_requests_mono (h : Step cfg s t) : s.requests ⊆ t.requests := by
  cases h with
  | receive => exact List.subset_cons_of_subset _ (fun _ h => h)
  | _ => exact fun _ h => h

theorem step_received_mono (h : Step cfg s t) {request : Request}
    (hs : Received s request) : Received t request := by
  obtain ⟨payload, member⟩ := hs
  exact ⟨payload, step_requests_mono h member⟩

/-- The event records the leader at dispatch time, not the current leader. -/
theorem only_leader_dispatches (h : Reachable cfg leader s) :
    ∀ d ∈ s.dispatches, d.2.2 = some d.1 := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | dispatch n request leader _ _ _ =>
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact leader
          · exact ih d hd
      | _ => exact ih

/-- Physical calls must correspond to a received logical invocation. -/
theorem no_dispatch_before_receipt (h : Reachable cfg leader s) :
    ∀ d ∈ s.dispatches, Received s d.2.1 := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | receive =>
          intro d hd
          obtain ⟨payload, member⟩ := ih d hd
          exact ⟨payload, List.mem_cons_of_mem _ member⟩
      | dispatch n request _ _ received _ =>
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact received
          · exact ih d hd
      | _ => exact ih

theorem executions_dispatched (h : Reachable cfg leader s) :
    ∀ e ∈ s.executions, ∃ l, (e.1, e.2.1, l) ∈ s.dispatches := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | dispatch =>
          intro e he
          obtain ⟨l, hl⟩ := ih e he
          exact ⟨l, List.mem_cons_of_mem _ hl⟩
      | respond n request value dispatched _ =>
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact dispatched
          · exact ih e he
      | _ => exact ih

theorem executions_observed (h : Reachable cfg leader s) :
    ∀ e ∈ s.executions, (e.2.1, e.2.2) ∈ s.observed := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | respond =>
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih e he)
      | _ => exact ih

theorem observed_executed (h : Reachable cfg leader s) :
    ∀ item ∈ s.observed, ∃ n, (n, item.1, item.2) ∈ s.executions := by
  induction h with
  | init => simp [initial]
  | step _ step ih =>
      cases step with
      | respond n request value _ _ =>
          intro item hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact ⟨n, List.mem_cons_self⟩
          · obtain ⟨n, hn⟩ := ih item hi
            exact ⟨n, List.mem_cons_of_mem _ hn⟩
      | _ => exact ih

theorem proposal_validity (h : Reachable cfg leader s) : s.proposed ⊆ s.observed := by
  induction h with
  | init => simp [initial]
  | step reach step ih =>
      cases step with
      | respond => exact fun _ hm => List.mem_cons_of_mem _ (ih hm)
      | propose n request value _ _ executed _ =>
          intro item hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact executions_observed reach _ executed
          · exact ih hi
      | repropose n request value _ _ executed _ =>
          intro item hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact executions_observed reach _ executed
          · exact ih hi
      | _ => exact ih

theorem consensus_validity (h : Reachable cfg leader s) : s.core.log.flatten ⊆ s.proposed := by
  induction h with
  | init => simp [initial, Resdet.initial]
  | step _ step ih =>
      cases step with
      | propose => exact fun _ hm => List.mem_cons_of_mem _ (ih hm)
      | repropose => exact fun _ hm => List.mem_cons_of_mem _ (ih hm)
      | decide batch valid =>
          intro item hi
          simp only [appendBatch, List.flatten_append, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.mem_append] at hi
          exact hi.elim (fun hm => ih hm) (valid item)
      | _ => exact ih

theorem leader_without_crashes (h : Reachable cfg leader s) (hc : cfg.crashes = false) :
    s.leader = some leader := by
  induction h with
  | init => rfl
  | step _ step ih =>
      cases step with
      | crash n enabled _ => cases enabled.symm.trans hc
      | elect n enabled _ _ => cases enabled.symm.trans hc
      | _ => exact ih

theorem senders_without_crashes (h : Reachable cfg leader s) (hc : cfg.crashes = false) :
    ∀ d ∈ s.dispatches, d.1 = leader := by
  induction h with
  | init => simp [initial]
  | step reach step ih =>
      cases step with
      | dispatch n request lead _ _ _ =>
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact Option.some.inj (lead.symm.trans (leader_without_crashes reach hc))
          · exact ih d hd
      | _ => exact ih

/-- With one fixed leader, its local deduplication prevents repeated dispatch. -/
theorem at_most_one_physical_dispatch (h : Reachable cfg leader s)
    (stable : cfg.crashes = false) : (s.dispatches.map fun d => d.2.1).Nodup := by
  induction h with
  | init => simp [initial]
  | step reach step ih =>
      cases step with
      | dispatch n request lead _ _ fresh =>
          simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, ih⟩
          intro hm
          obtain ⟨d, hd, sameRequest⟩ := List.mem_map.mp hm
          have currentLeader : n = leader :=
            Option.some.inj (lead.symm.trans (leader_without_crashes reach stable))
          have sameSender : d.1 = n :=
            (senders_without_crashes reach stable d hd).trans currentLeader.symm
          rcases d with ⟨sender, rid, snapshot⟩
          simp only at sameRequest sameSender
          subst sender rid
          exact fresh snapshot hd
      | _ => exact ih

/-- Physical provenance and a received invocation, in addition to log validity. -/
theorem response_validity (h : Reachable cfg leader s) (r : Node)
    {item : Item Request Response} (hi : item ∈ (s.core.replica r).delivered) :
    item ∈ s.observed ∧ Received s item.1 ∧
      ∃ n l, (n, item.1, item.2) ∈ s.executions ∧ (n, item.1, l) ∈ s.dispatches := by
  have observed := proposal_validity h (consensus_validity h
    (Resdet.delivered_in_log (reachable_refines h) r hi))
  obtain ⟨n, executed⟩ := observed_executed h item observed
  obtain ⟨l, dispatched⟩ := executions_dispatched h _ executed
  exact ⟨observed, no_dispatch_before_receipt h _ dispatched, n, l, executed, dispatched⟩

theorem response_agreement (h : Reachable cfg leader s) (left right : Node)
    {request : Request} {a b : Response}
    (ha : (request, a) ∈ (s.core.replica left).delivered)
    (hb : (request, b) ∈ (s.core.replica right).delivered) : a = b :=
  Resdet.response_agreement (reachable_refines h) left right ha hb

theorem at_most_once_delivery (h : Reachable cfg leader s) (r : Node) :
    ((s.core.replica r).delivered.map Prod.fst).Nodup :=
  Resdet.at_most_once_delivery (reachable_refines h) r

theorem prefix_agreement (h : Reachable cfg leader s) (left right : Node) :
    (s.core.replica left).delivered <+: (s.core.replica right).delivered ∨
    (s.core.replica right).delivered <+: (s.core.replica left).delivered :=
  Resdet.prefix_agreement (reachable_refines h) left right

theorem race_winner_agreement (h : Reachable cfg leader s) (left right : Node)
    {a b : Item Request Response}
    (ha : (s.core.replica left).delivered.head? = some a)
    (hb : (s.core.replica right).delivered.head? = some b) : a.1 = b.1 :=
  Resdet.race_winner_agreement (reachable_refines h) left right ha hb

theorem applied_prefix_correct (h : Reachable cfg leader s) (r : Node) :
    (s.core.replica r).delivered = dedup (s.core.log.take (s.core.replica r).processed).flatten :=
  (Resdet.reachable_invariant (reachable_refines h)).appliedPrefixCorrect r

/-- Resdet safety obligations. Unique physical dispatch requires crashes disabled. -/
structure Safety (cfg : Config) (s : State Node Request Payload Response) : Prop where
  receiptBeforeDispatch : ∀ d ∈ s.dispatches, Received s d.2.1
  authorizedDispatch : ∀ d ∈ s.dispatches, d.2.2 = some d.1
  observedExecution : ∀ item ∈ s.observed, ∃ n, (n, item.1, item.2) ∈ s.executions
  executionDispatch : ∀ e ∈ s.executions, ∃ l, (e.1, e.2.1, l) ∈ s.dispatches
  proposalValidity : s.proposed ⊆ s.observed
  consensusValidity : s.core.log.flatten ⊆ s.proposed
  physicalOnce : cfg.crashes = false → (s.dispatches.map fun d => d.2.1).Nodup
  dedupConsistent : DedupConsistent s
  contiguousPrefix : Resdet.Invariant s.core
  deliveryOnce : ∀ r, ((s.core.replica r).delivered.map Prod.fst).Nodup
  agreement : ∀ left right request a b,
    (request, a) ∈ (s.core.replica left).delivered →
    (request, b) ∈ (s.core.replica right).delivered → a = b
  prefixes : ∀ left right,
    (s.core.replica left).delivered <+: (s.core.replica right).delivered ∨
    (s.core.replica right).delivered <+: (s.core.replica left).delivered
  noEarlyDelivery : ∀ r item, item ∈ (s.core.replica r).delivered → item ∈ s.core.log.flatten

theorem all_safety (h : Reachable cfg leader s) : Safety cfg s :=
  { receiptBeforeDispatch := no_dispatch_before_receipt h
    authorizedDispatch := only_leader_dispatches h
    observedExecution := observed_executed h
    executionDispatch := executions_dispatched h
    proposalValidity := proposal_validity h
    consensusValidity := consensus_validity h
    physicalOnce := at_most_one_physical_dispatch h
    dedupConsistent := reachable_dedup_consistent h
    contiguousPrefix := Resdet.reachable_invariant (reachable_refines h)
    deliveryOnce := at_most_once_delivery h
    agreement := fun l r _ _ _ ha hb => response_agreement h l r ha hb
    prefixes := prefix_agreement h
    noEarlyDelivery := fun r _ hi => Resdet.delivered_in_log (reachable_refines h) r hi }

end Resdet.Protocol
