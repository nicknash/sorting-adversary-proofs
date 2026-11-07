import SortingAdversary.Optimal.TreeRouter
import SortingAdversary.Optimal.LocalChoice

/-!
# The actual safe stopping sign and its retained fraction

The executable routing tests decide the forced branches. Only when both
branches are safe does the rule compare the two rational local estimates.
The checked no-common-child condition rules out delegation at this point.
-/

namespace SortingAdversary.Optimal.PoolTree.Tree

open PoolState WeakMaps WeakMaps.WeakSystem ControllerRouting Safety PoolPalette LocalChoice
variable {n : ℕ}

theorem closedAdd_count_eq (p : Pool n) (a b : Fin n) :
    (closedAdd p.system a b).count = (p.system.addRow a b).count := by
  apply congrArg Finset.card
  ext f
  simp only [mem_maps, closedAdd_valid _ p.invariant.closed, valid_addRow]

structure Estimates (p : Pool n) (a b : Fin n) (error : ℚ) where
  forward : ℚ
  reverse : ℚ
  forward_error : |forward - weakProbability p.system a b| ≤ error
  reverse_error : |reverse - weakProbability p.system b a| ≤ error

structure StoppingSign (p : Pool n) (a b : Fin n) (error : ℚ) where
  forward : Bool
  safe : Safe p.system p.pins (firstLabel a b forward) (secondLabel a b forward)
  feasible : ∃ f, (closedAdd p.system (firstLabel a b forward) (secondLabel a b forward)).Valid f
  retention : (1 / 2 - error) * (p.system.count : ℚ) ≤
    (closedAdd p.system (firstLabel a b forward) (secondLabel a b forward)).count

theorem retaining_fraction (p : Pool n) (a b : Fin n) (error : ℚ) (he : 0 ≤ error)
    (hr : RetainsAll p.system a b) :
    (1 / 2 - error) * (p.system.count : ℚ) ≤ (closedAdd p.system a b).count := by
  rw [retaining_count p a b hr]
  have hp : (0 : ℚ) ≤ p.system.count := Nat.cast_nonneg _
  nlinarith

def chooseStoppingSign (p : Pool n) (a b : Fin n)
    (hab : p.system.edge a b ≠ true) (hba : p.system.edge b a ≠ true)
    (hstop : ¬ ∃ c, p.pins a = some c ∧ p.pins b = some c)
    (error : ℚ) (he : 0 ≤ error) (estimates : Estimates p a b error) : StoppingSign p a b error :=
  let decision := chooseRoute p.system p.pins p.invariant a b hab hba
  match hdec : decision.val with
  | .forward =>
    have hs : RetainsAll p.system a b ∧ Safe p.system p.pins a b := by
      simpa only [hdec, Specification] using decision.property
    ⟨true, hs.2, retaining_feasible p.invariant hs.1, retaining_fraction p a b error he hs.1⟩
  | .reverse =>
    have hs : RetainsAll p.system b a ∧ Safe p.system p.pins b a := by
      simpa only [hdec, Specification] using decision.property
    ⟨false, hs.2, retaining_feasible p.invariant hs.1, retaining_fraction p b a error he hs.1⟩
  | .delegate =>
    False.elim (hstop (by simpa only [hdec, Specification] using decision.property))
  | .compareMasses =>
    have hs : Safe p.system p.pins a b ∧ Safe p.system p.pins b a ∧
        (∃ f, (closedAdd p.system a b).Valid f) ∧
          (∃ f, (closedAdd p.system b a).Valid f) := by
      simpa only [hdec, Specification] using decision.property
    have hfrac := approximate_larger_branch p.system a b p.count_pos
      estimates.forward estimates.reverse error estimates.forward_error estimates.reverse_error
    have hp : (0 : ℚ) < p.system.count := by exact_mod_cast p.count_pos
    if hchoose : estimates.reverse ≤ estimates.forward then
      { forward := true
        safe := hs.1
        feasible := hs.2.2.1
        retention := by
          change (1 / 2 - error) * (p.system.count : ℚ) ≤ (closedAdd p.system a b).count
          rw [closedAdd_count_eq]
          apply (le_div_iff₀ hp).mp
          simpa only [chooseFromEstimates, if_pos hchoose] using hfrac }
    else
      { forward := false
        safe := hs.2.1
        feasible := hs.2.2.2
        retention := by
          change (1 / 2 - error) * (p.system.count : ℚ) ≤ (closedAdd p.system b a).count
          rw [closedAdd_count_eq]
          apply (le_div_iff₀ hp).mp
          simpa only [chooseFromEstimates, if_neg hchoose] using hfrac }

theorem stopNode_bounded (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (hi : Invariant (closedAdd p.system a b) p.pins)
    (h : TreeBounded (Tree.node identity p children)) :
    TreeBounded (stopNode identity p children a b ha hb hi) := by
  obtain ⟨hp, hc⟩ := (treeBounded_node_iff _ _ _).mp h
  exact (treeBounded_node_iff _ _ _).mpr ⟨hp, hc⟩

theorem stopNode_retention (identity : ℕ) (p : Pool n) (children : List (ℕ × Tree n))
    (a b : Fin n) (ha : a ∈ p.members) (hb : b ∈ p.members)
    (hi : Invariant (closedAdd p.system a b) p.pins) (fraction : ℚ) (hf : 0 < fraction)
    (hr : fraction * (p.system.count : ℚ) ≤ (closedAdd p.system a b).count) :
    ((Tree.node identity p children).count : ℚ) ≤
      (1 / fraction) * (stopNode identity p children a b ha hb hi).count := by
  have hprice : (p.system.count : ℚ) ≤ (1 / fraction) * (closedAdd p.system a b).count := by
    calc
      (p.system.count : ℚ) ≤ (closedAdd p.system a b).count / fraction :=
        (le_div_iff₀ hf).mpr (by simpa only [mul_comm] using hr)
      _ = (1 / fraction) * (closedAdd p.system a b).count := by ring
  rw [stopNode, count, count]
  change (↑(p.system.count * (children.map (fun a => a.2.count)).prod) : ℚ) ≤
    (1 / fraction) * ↑((closedAdd p.system a b).count * (children.map (fun a => a.2.count)).prod)
  rw [Nat.cast_mul, Nat.cast_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hprice
    (Nat.cast_nonneg (children.map (fun a => a.2.count)).prod : (0 : ℚ) ≤ _)

/-- Answer the unknown query at its actual stopping node, before repairs. -/
def stoppingComparison {Payload : Type*} (payload : Payload)
    (t : Tree n) (h : t.WellFormed) (ho : t.Coherent)
    (a b : Fin n) (ha : a ∈ t.pool.members) (hb : b ∈ t.pool.members)
    (hab : t.pool.system.edge a b ≠ true) (hba : t.pool.system.edge b a ≠ true)
    (hstop : ¬ ∃ c, t.pool.pins a = some c ∧ t.pool.pins b = some c)
    (error : ℚ) (he : 0 ≤ error) (hehalf : error < 1 / 2)
    (estimates : Estimates t.pool a b error) : Answered Payload t a b :=
  match t with
  | .node identity p children =>
    let sign := chooseStoppingSign p a b hab hba hstop error he estimates
    let first := firstLabel a b sign.forward
    let second := secondLabel a b sign.forward
    let hf := first_member p a b ha hb sign.forward
    let hs := second_member p a b ha hb sign.forward
    let hi := safe_update p.invariant (reverse_unknown p a b hab hba sign.forward)
      sign.safe sign.feasible
    { forward := sign.forward
      next := stopNode identity p children first second hf hs hi
      payload := payload
      charge := 1 / (1 / 2 - error)
      wellFormed := stopNode_wellFormed identity p children (parts h) first second hf hs hi
      coherent := stopNode_coherent identity p children (parts h) ho first second hf hs hi sign.safe.1
      bounded := stopNode_bounded identity p children first second hf hs hi
      members := rfl
      edges := rfl
      retention := stopNode_retention identity p children first second hf hs hi
        (1 / 2 - error) (by linarith) sign.retention }

/-- Any subsequent finite local repair execution has this interface when
replayed into the tree. It retains the public answer and original membership. -/
structure Maintenance (Payload : Type*) (t : Tree n) where
  next : Tree n
  payload : Payload
  charge : ℚ
  wellFormed : next.WellFormed
  coherent : next.Coherent
  bounded : TreeBounded t → TreeBounded next
  members : next.pool.members = t.pool.members
  edges : next.pool.system.edge = t.pool.system.edge
  retention : (t.count : ℚ) ≤ charge * next.count

def Answered.maintain {Payload Extra : Type*} {t : Tree n} {a b : Fin n}
    (r : Answered Payload t a b) (m : Maintenance Extra r.next) :
    Answered (Payload × Extra) t a b where
  forward := r.forward
  next := m.next
  payload := (r.payload, m.payload)
  charge := r.charge * m.charge
  wellFormed := m.wellFormed
  coherent := m.coherent
  bounded := fun h => m.bounded (r.bounded h)
  members := m.members.trans r.members
  edges := m.edges.trans r.edges
  retention := by
    calc
      (t.count : ℚ) ≤ r.charge * r.next.count := r.retention
      _ ≤ r.charge * (m.charge * m.next.count) :=
        mul_le_mul_of_nonneg_left m.retention r.charge_pos.le
      _ = (r.charge * m.charge) * m.next.count := (mul_assoc _ _ _).symm

end SortingAdversary.Optimal.PoolTree.Tree
