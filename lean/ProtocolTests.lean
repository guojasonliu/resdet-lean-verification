import Resdet

namespace Resdet.Protocol.Tests

abbrev S := State Bool Nat Nat Nat
def cfg : Config := ⟨1, by decide, true, false⟩
def p0 : S := initial false
def p1 := { p0 with ballots := [(false, 1, 42)] }
def p2 := { p1 with choices := [(1, 42, false)] }
def p3 := { p2 with dispatches := [(false, 1, some false)] }
def p4 := { p3 with executions := [(false, 1, 7)], observed := [(1, 7)] }
def p5 := { p4 with proposed := [(1, 7)] }
def p6 := { p5 with up := fun r => if r = false then false else p5.up r, leader := none }
def p7 := { p6 with leader := some true }
def p8 := { p7 with dispatches := (true, 1, some true) :: p7.dispatches }
def p9 := { p8 with
  executions := (true, 1, 9) :: p8.executions
  observed := (1, 9) :: p8.observed }
def p10 := { p9 with proposed := (1, 9) :: p9.proposed }
-- Consensus can order the second physical result first.
def batch : List (Item Nat Nat) := [(1, 9), (1, 7)]
def p11 := { p10 with core := appendBatch p10.core batch }
def p12 := { p11 with core := learnSlot p11.core true 0 }
def p13 := process p12 true batch
def p14 := { p13 with up := fun r => if r = false then true else p13.up r }
def p15 := { p14 with core := learnSlot p14.core false 0 }
def p16 := process p15 false batch

/-- The retained-state recovery example, followed by stuttering. -/
def recoveryTrace : Nat → S
  | 0 => p0
  | 1 => p1
  | 2 => p2
  | 3 => p3
  | 4 => p4
  | 5 => p5
  | 6 => p6
  | 7 => p7
  | 8 => p8
  | 9 => p9
  | 10 => p10
  | 11 => p11
  | 12 => p12
  | 13 => p13
  | 14 => p14
  | 15 => p15
  | _ + 16 => p16

theorem recovery_behavior : Behavior cfg false recoveryTrace := by
  constructor
  · rfl
  · intro t
    match t with
    | 0 =>
        exact .vote p0 false 1 42 (by decide) (by simp [p0, initial])
    | 1 =>
        exact .select p1 false 1 42 false (by decide) (by decide)
            (by simp [Selected, p1, p0, initial])
            ⟨[false], by decide, by decide, by decide⟩ (by decide)
    | 2 =>
        exact .dispatch p2 false 1 (by decide) (by decide)
            ⟨42, false, by decide⟩ (by simp [p2, p1, p0, initial])
    | 3 =>
        exact .respond p3 false 1 7 ⟨some false, by decide⟩
            (by simp [p3, p2, p1, p0, initial])
    | 4 =>
        exact .propose p4 false 1 7 (by decide) (by decide) (by decide) (by decide)
    | 5 =>
        exact .crash p5 false (by decide) (by decide)
    | 6 =>
        exact .elect p6 true (by decide) (by decide) (by decide)
    | 7 =>
        exact .dispatch p7 true 1 (by decide) (by decide)
            ⟨42, false, by decide⟩ (by simp [p7, p6, p5, p4, p3])
    | 8 =>
        exact .respond p8 true 1 9 ⟨some true, by decide⟩
            (by simp [p8, p7, p6, p5, p4])
    | 9 =>
        exact .propose p9 true 1 9 (by decide) (by decide) (by decide) (by decide)
    | 10 =>
        exact .decide p10 batch (by
            intro item hi
            simpa [batch, p10, p9, p8, p7, p6, p5] using hi)
    | 11 =>
        exact .learn p11 true 0 (by decide) (by decide)
    | 12 =>
        exact .process p12 true batch (by decide) (by decide) (by decide)
    | 13 =>
        exact .recover p13 false (by decide) (by decide)
    | 14 =>
        exact .learn p14 false 0 (by decide) (by decide)
    | 15 =>
        exact .process p15 false batch (by decide) (by decide) (by decide)
    | _ + 16 =>
        exact .stutter _

theorem recovery_run : Reachable cfg false p16 :=
  recovery_behavior.reachable 16

theorem recoveryTrace_steady {t : Nat} (h : 16 ≤ t) : recoveryTrace t = p16 := by
  have eq : t = (t - 16) + 16 := by omega
  rw [eq]
  rfl

/-- Leadership stabilizes before the retry and before either response is agreed. -/
theorem recovery_stable : StableLeader recoveryTrace true 7 := by
  intro t ht
  by_cases done : 16 ≤ t
  · rw [recoveryTrace_steady done]
    decide
  · have finite : ∀ t : Fin 16, 7 ≤ t.val →
        (recoveryTrace t.val).leader = some true ∧ (recoveryTrace t.val).up true = true := by decide
    exact finite ⟨t, by omega⟩ ht

theorem pending_at_stabilization : ¬ Agreed (recoveryTrace 7) 1 := by
  unfold Agreed
  decide

theorem stable_leader_attempts_pending_request :
    ProposalAttempt recoveryTrace 9 true (1, 9) ∧ ¬ Agreed (recoveryTrace 9) 1 := by
  unfold ProposalAttempt Agreed
  decide

theorem recovered_replicas_agree :
    (p16.core.replica false).delivered = [(1, 9)] ∧
    (p16.core.replica true).delivered = [(1, 9)] ∧ p16.seen false = [1] ∧
    p16.seen true = [1] := by decide

theorem physical_execution_can_repeat : p16.dispatches.length = 2 ∧
    ¬ (p16.dispatches.map fun d => d.2.1).Nodup := by decide

theorem reproposal_reachable : Reachable cfg false
    { p16 with proposed := (1, 9) :: p16.proposed } :=
  .step recovery_run (.repropose p16 true 1 9 (by decide) (by decide) (by decide) (by decide))

theorem two_distinct_matching_voters :
    Justified 2 [(false, 1, 42), (true, 1, 42)] (1, 42, false) :=
  ⟨[false, true], by decide, by decide, by decide⟩

/-- Repeating one caller's vote cannot satisfy a two-caller quorum. -/
theorem invalid_double_counting :
    ¬ Justified 2 [(false, 1, 42), (false, 1, 42)] (1, 42, false) := by
  intro h
  obtain ⟨voters, unique, enough, matching⟩ := h
  cases voters with
  | nil => simp at enough
  | cons a rest =>
      have ha : a = false := by simpa using matching a (by simp)
      cases rest with
      | nil => simp at enough
      | cons b tail =>
          have hb : b = false := by simpa using matching b (by simp)
          have fresh := (List.nodup_cons.mp unique).1
          exact fresh (by simp [ha, hb])

def fallbackCfg : Config := ⟨2, by decide, false, true⟩
def f0 : S := initial false
def f1 := { f0 with ballots := [(false, 1, 42)] }
def f2 := { f1 with choices := [(1, 42, true)] }

theorem fallback_run : Reachable fallbackCfg false f2 := by
  have h1 : Reachable fallbackCfg false f1 := .step .init (.vote f0 false 1 42
    (by decide) (by simp [f0, initial]))
  exact .step h1 (.select f1 false 1 42 true (by decide) (by decide)
    (by simp [Selected, f1, f0, initial]) ⟨false, by decide⟩ (by decide))

theorem fallback_is_marked : (1, 42, true) ∈ f2.choices := by decide

-- A valid infinite core execution which learns but never processes.
def waiting0 : Resdet.State Bool Nat Nat := Resdet.initial
def waiting1 := appendBatch waiting0 [(1, 7)]
def waiting2 := learnSlot waiting1 false 0
def waitingTrace : Nat → Resdet.State Bool Nat Nat
  | 0 => waiting0
  | 1 => waiting1
  | _ + 2 => waiting2

theorem waiting_behavior : Resdet.Behavior waitingTrace := by
  constructor
  · rfl
  · intro t
    cases t with
    | zero => exact .append _ [(1, 7)]
    | succ t =>
        cases t with
        | zero => exact .learn _ false 0 (by decide)
        | succ t => exact .stutter _

theorem waiting_never_delivers (t : Nat) : (waitingTrace t |>.replica false).delivered = [] := by
  cases t with
  | zero => rfl
  | succ t => cases t <;> rfl

theorem fairness_is_necessary : ¬ DeliveryProgress waitingTrace false := by
  intro progress
  obtain ⟨t, _, value, delivered⟩ := agreed_eventually_delivered waiting_behavior false
    progress 1 (request := 1) (by decide)
  rw [waiting_never_delivers] at delivered
  simp at delivered

theorem fair_if_eventually_always {enabled occurs : Nat → Prop} (finish : Nat)
    (steady : ∀ t, finish ≤ t → occurs t) : WeakFair enabled occurs := by
  intro start _
  exact ⟨max start finish, Nat.le_max_left _ _, steady _ (Nat.le_max_right _ _)⟩

/-- The recovery trace satisfies the progress contracts from the new leader's
election at time 7, while request 1 is still pending (see the facts above). -/
theorem progress_contracts_satisfiable : ∃ (tr : Nat → S) (finish : Nat),
    Behavior cfg false tr ∧ StableLeader tr true finish ∧ GateReady cfg (tr finish) 1 ∧
    LocalProgress cfg tr true 1 ∧ ConsensusProgress tr ∧
    ∀ r, DeliveryProgress (fun t => (tr t).core) r := by
  let tr := recoveryTrace
  let finish := 16
  have b : Behavior cfg false tr := recovery_behavior
  have steady : ∀ t, finish ≤ t → tr t = p16 := fun _ ht => recoveryTrace_steady ht
  have ready : GateReady cfg (tr 7) 1 :=
    ⟨42, false, ⟨[false], by decide, by decide, by decide⟩, by decide⟩
  have localP : LocalProgress cfg tr true 1 := by
    refine { select := ?_, dispatch := ?_, respond := ?_, propose := ?_ }
    · apply fair_if_eventually_always finish
      intro t ht
      rw [steady (t+1) (by omega)]
      exact ⟨42, false, by decide⟩
    · apply fair_if_eventually_always finish
      intro t ht
      rw [steady (t+1) (by omega)]
      exact ⟨some true, by decide⟩
    · apply fair_if_eventually_always finish
      intro t ht
      rw [steady (t+1) (by omega)]
      exact ⟨9, by decide⟩
    · apply fair_if_eventually_always finish
      intro t ht
      rw [steady (t+1) (by omega)]
      exact ⟨9, by decide⟩
  have consensus : ConsensusProgress tr := by
    intro start item hi
    let t := max start finish
    have sub : (tr start).proposed ⊆ (tr t).proposed :=
      propagate (p := fun u => (tr start).proposed ⊆ (tr u).proposed)
        (fun u hs _ hm => proposals_step_mono (b.next u) (hs hm))
        (Nat.le_max_left _ _) (fun _ h => h)
    have itemFinal : item ∈ p16.proposed := by
      rw [← steady t (Nat.le_max_right _ _)]
      exact sub hi
    refine ⟨t, Nat.le_max_left _ _, ?_⟩
    change item ∈ (tr t).core.log.flatten
    rw [steady t (Nat.le_max_right _ _)]
    exact (show p16.proposed = p16.core.log.flatten from by decide) ▸ itemFinal
  refine ⟨tr, 7, b, recovery_stable, ready, localP, consensus, ?_⟩
  intro r
  constructor
  · intro start slot hs
    let t := max start finish
    have bound := (b.core.log_mono (Nat.le_max_left start finish)).length_le
    change (tr start).core.log.length ≤ (tr t).core.log.length at bound
    rw [steady t (Nat.le_max_right _ _)] at bound
    have len : p16.core.log.length = 1 := by decide
    rw [len] at bound
    have eq : slot = 0 := by omega
    refine ⟨t, Nat.le_max_left _ _, ?_⟩
    change slot ∈ ((tr t).core.replica r).learned
    rw [steady t (Nat.le_max_right _ _), eq]
    cases r <;> decide
  · intro start enabled
    have en := enabled (max start finish) (Nat.le_max_left _ _)
    change ((tr (max start finish)).core.replica r).processed <
      (tr (max start finish)).core.log.length ∧ _ at en
    rw [steady _ (Nat.le_max_right _ _)] at en
    have impossible : ¬ (p16.core.replica r).processed < p16.core.log.length := by
      cases r <;> decide
    exact False.elim (impossible en.1)

/-- The weaker stable-leader consensus version also has jointly satisfiable
premises, not only the global-buffer version. -/
theorem retry_contracts_satisfiable : ∃ (tr : Nat → S) (finish : Nat),
    Behavior cfg false tr ∧ StableLeader tr true finish ∧ GateReady cfg (tr finish) 1 ∧
    RetryProgress cfg tr true 1 ∧ StableConsensusProgress tr true finish ∧
    ∀ r, DeliveryProgress (fun t => (tr t).core) r := by
  obtain ⟨tr, finish, b, stable, ready, localP, consensus, delivery⟩ := progress_contracts_satisfiable
  have ingress : EventuallyFrom 0 (fun t => GateReady cfg (tr t) 1) :=
    ⟨finish, Nat.zero_le _, ready⟩
  obtain ⟨d, _, value, delivered⟩ := eventual_delivery b finish stable 1 ingress localP consensus
    false (delivery false)
  have agreedAtD : Agreed (tr d) 1 := List.mem_map_of_mem
    (Resdet.delivered_in_log (reachable_refines (b.reachable d)) false delivered)
  have retry : RetryProgress cfg tr true 1 := by
    refine ⟨localP.toHandlerProgress, ?_⟩
    intro start enabled
    let t := max start d
    have en := enabled t (Nat.le_max_left _ _)
    have agreed : Agreed (tr t) 1 :=
      ((Resdet.flatten_prefix (b.core.log_mono (Nat.le_max_right start d))).map Prod.fst).subset agreedAtD
    exact False.elim (en.2.2.2 agreed)
  have stableCG : StableConsensusProgress tr true finish := by
    intro t _ item attempt
    have proposed : item ∈ (tr (t+1)).proposed := by
      rw [attempt.2.2]
      exact List.mem_cons_self
    obtain ⟨u, hu, agreed⟩ := consensus (t+1) item proposed
    exact ⟨u, by omega, agreed⟩
  exact ⟨tr, finish, b, stable, ready, retry, stableCG, delivery⟩

end Resdet.Protocol.Tests
