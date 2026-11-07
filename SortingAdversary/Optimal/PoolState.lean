import SortingAdversary.Optimal.Promotion
import SortingAdversary.Optimal.Endpoints

/-!+# Stored pools with actual membership and certified transitions

All pools use the original finite label carrier. Membership is explicit:
labels that have never entered a pool are isolated dummy coordinates, not
physical child members. Admissions therefore cannot unpin an old member.
The executable admission operation appends a position exactly when required
by the next admission number, and proves its exact multiplier on the count.
-/

namespace SortingAdversary.Optimal.PoolState

set_option maxHeartbeats 800000

open WeakMaps WeakMaps.WeakSystem FiniteRefinement ControllerRouting
open FreshAdmission PinTransitions RefinementTransitions

/-- A concrete local pool on the original label carrier. -/
structure Pool (n : ℕ) where
  palette : ℕ
  positive : 0 < palette
  members : Finset (Fin n)
  system : WeakSystem (Fin n) (palette + 1)
  pins : Fin n → Option (Fin (palette + 1))
  invariant : Invariant system pins
  pin_bounds : PinBounds system pins
  capacity : members.card ≤ palette + 1
  outside : ∀ x, x ∉ members →
    pins x = some (system.lower x) ∧ Unused system x (system.lower x)

namespace Pool

variable {n : ℕ}

def free (p : Pool n) : Finset (Fin n) := p.members.filter (fun x => p.pins x = none)
def fixed (p : Pool n) : Finset (Fin n) := p.members.filter (fun x => p.pins x ≠ none)

theorem free_member (p : Pool n) {v : Fin n} (hv : p.pins v = none) : v ∈ p.members := by
  by_contra hm
  have h := (p.outside v hm).1
  rw [hv] at h
  contradiction

theorem free_iff (p : Pool n) (v : Fin n) : v ∈ p.free ↔ p.pins v = none := by
  simp only [free, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨p.free_member h, h⟩⟩

theorem count_pos (p : Pool n) : 0 < p.system.count :=
  p.system.count_pos_iff.mpr p.invariant.feasible

/-- Append one top position without changing any old endpoint or law. -/
def append (p : Pool n) : Pool n where
  palette := p.palette + 1
  positive := Nat.succ_pos _
  members := p.members
  system := p.system.enlarge
  pins := mapPins Fin.castSucc p.pins
  invariant := enlargement_invariant p.invariant p.pin_bounds
  pin_bounds := enlargement_pin_bounds p.pin_bounds
  capacity := p.capacity.trans (Nat.le_succ _)
  outside := by
    intro x hx
    obtain ⟨hpin, hu⟩ := p.outside x hx
    constructor
    · simp [mapPins, hpin, enlarge]
    · refine ⟨rfl, ?_, hu.outgoing, hu.incoming⟩
      exact congrArg Fin.castSucc hu.upper

@[simp] theorem append_count (p : Pool n) : p.append.system.count = p.system.count :=
  count_enlarge p.system

@[simp] theorem append_members (p : Pool n) : p.append.members = p.members := rfl

@[simp] theorem append_free (p : Pool n) : p.append.free = p.free := by
  ext v
  rw [free_iff, free_iff]
  change (p.pins v).map Fin.castSucc = none ↔ p.pins v = none
  cases p.pins v <;> simp

/-- Admit a genuinely unused label once the palette can pay its birthday. -/
def admitSized (p : Pool n) (v : Fin n) (hv : v ∉ p.members)
    (hcap : p.members.card + 1 ≤ p.palette + 1) : Pool n where
  palette := p.palette
  positive := p.positive
  members := insert v p.members
  system := admit p.system v
  pins := unpin p.pins v
  invariant := admission_invariant p.invariant (p.outside v hv).2 p.positive
  pin_bounds := admission_pin_bounds p.pin_bounds v
  capacity := by simpa [Finset.card_insert_of_notMem hv] using hcap
  outside := by
    intro x hx
    have hxv : x ≠ v := fun h => hx (Finset.mem_insert.mpr (Or.inl h))
    have hxm : x ∉ p.members := fun h => hx (Finset.mem_insert.mpr (Or.inr h))
    obtain ⟨hpin, hu⟩ := p.outside x hxm
    constructor
    · simpa [unpin, admit, hxv] using hpin
    · refine ⟨rfl, ?_, hu.outgoing, hu.incoming⟩
      simpa [admit, hxv] using hu.upper

@[simp] theorem admitSized_count (p : Pool n) (v : Fin n) (hv : v ∉ p.members)
    (hcap : p.members.card + 1 ≤ p.palette + 1) :
    (p.admitSized v hv hcap).system.count = p.system.count * (p.palette + 1) :=
  admission_count (p.outside v hv).2

@[simp] theorem admitSized_free (p : Pool n) (v : Fin n) (hv : v ∉ p.members)
    (hcap : p.members.card + 1 ≤ p.palette + 1) :
    (p.admitSized v hv hcap).free = insert v p.free := by
  ext x
  rw [free_iff]
  simp only [admitSized, unpin, Finset.mem_insert, free_iff]
  by_cases hx : x = v <;> simp [hx]

/-- Exact executable birthday rule. At most one append is necessary because
the old palette already dominates the previous number of admissions. -/
def admitFresh (p : Pool n) (v : Fin n) (hv : v ∉ p.members) : Pool n :=
  if hcap : p.members.card + 1 ≤ p.palette + 1 then p.admitSized v hv hcap
  else p.append.admitSized v (by simpa only [append_members] using hv) (by
    change p.members.card + 1 ≤ p.palette + 1 + 1
    exact Nat.succ_le_succ p.capacity)

@[simp] theorem admitFresh_members (p : Pool n) (v : Fin n) (hv : v ∉ p.members) :
    (p.admitFresh v hv).members = insert v p.members := by
  unfold admitFresh
  split <;> rfl

@[simp] theorem admitFresh_free (p : Pool n) (v : Fin n) (hv : v ∉ p.members) :
    (p.admitFresh v hv).free = insert v p.free := by
  unfold admitFresh
  split <;> simp only [admitSized_free, append_free]

theorem admitFresh_palette (p : Pool n) (v : Fin n) (hv : v ∉ p.members) :
    p.palette ≤ (p.admitFresh v hv).palette ∧
      (p.admitFresh v hv).palette ≤ p.palette + 1 := by
  unfold admitFresh
  split <;> simp [admitSized, append]

theorem admitFresh_count (p : Pool n) (v : Fin n) (hv : v ∉ p.members) :
    (p.admitFresh v hv).system.count =
      p.system.count * ((p.admitFresh v hv).palette + 1) := by
  by_cases hcap : p.members.card + 1 ≤ p.palette + 1
  · have heq : p.admitFresh v hv = p.admitSized v hv hcap := dif_pos hcap
    rw [heq]
    exact admitSized_count p v hv hcap
  · have heq : p.admitFresh v hv = p.append.admitSized v
        (by simpa only [append_members] using hv)
        (by exact Nat.succ_le_succ p.capacity) := dif_neg hcap
    rw [heq, admitSized_count, append_count]
    rfl

/-- The actual jth child admission supplies at least the multiplier j. -/
theorem birthday_credit (p : Pool n) (v : Fin n) (hv : v ∉ p.members) :
    (p.members.card + 1) * p.system.count ≤ (p.admitFresh v hv).system.count := by
  rw [admitFresh_count, Nat.mul_comm p.system.count]
  apply Nat.mul_le_mul_right
  have hc := (p.admitFresh v hv).capacity
  simpa [Finset.card_insert_of_notMem hv] using hc

/-- Admission data needed to transport a pool's already existing children
through the optional top-position append. -/
structure Admission (p : Pool n) (v : Fin n) where
  next : Pool n
  embed : Fin (p.palette + 1) → Fin (next.palette + 1)
  embed_strict : StrictMono embed
  members_eq : next.members = insert v p.members
  pin_new : next.pins v = none
  pin_old : ∀ x, x ≠ v → next.pins x = (p.pins x).map embed
  edges : next.system.edge = p.system.edge
  palette_bounds : p.palette ≤ next.palette ∧ next.palette ≤ p.palette + 1
  count_eq : next.system.count = p.system.count * (next.palette + 1)
  birthday : (p.members.card + 1) * p.system.count ≤ next.system.count

/-- Certified executable child admission, including the colour transport. -/
def admission (p : Pool n) (v : Fin n) (hv : v ∉ p.members) : Admission p v :=
  if hcap : p.members.card + 1 ≤ p.palette + 1 then
    { next := p.admitSized v hv hcap
      embed := id
      embed_strict := fun _ _ h => h
      members_eq := rfl
      pin_new := by simp [admitSized, unpin]
      pin_old := by
        intro x hx
        simp only [admitSized, unpin, Function.update_of_ne hx]
        cases p.pins x <;> rfl
      edges := rfl
      palette_bounds := ⟨le_rfl, Nat.le_succ _⟩
      count_eq := admitSized_count p v hv hcap
      birthday := by
        rw [admitSized_count, Nat.mul_comm p.system.count]
        exact Nat.mul_le_mul_right _ hcap }
  else
    let next := p.append.admitSized v (by simpa only [append_members] using hv)
      (by exact Nat.succ_le_succ p.capacity)
    { next := next
      embed := Fin.castSucc
      embed_strict := fun _ _ h => h
      members_eq := rfl
      pin_new := by simp [next, admitSized, unpin]
      pin_old := by
        intro x hx
        simp only [next, admitSized, unpin, Function.update_of_ne hx, append, mapPins]
      edges := rfl
      palette_bounds := ⟨Nat.le_succ _, le_rfl⟩
      count_eq := by
        change (p.append.admitSized v _ _).system.count = _
        rw [admitSized_count, append_count]
        rfl
      birthday := by
        change (p.members.card + 1) * p.system.count ≤ (p.append.admitSized v _ _).system.count
        rw [admitSized_count, append_count, Nat.mul_comm p.system.count]
        apply Nat.mul_le_mul_right
        exact Nat.succ_le_succ p.capacity }

theorem Admission.free_eq (p : Pool n) (v : Fin n) (a : Admission p v) :
    a.next.free = insert v p.free := by
  ext x
  rw [free_iff, Finset.mem_insert, free_iff]
  by_cases hx : x = v
  · subst x
    simp [a.pin_new]
  · rw [a.pin_old x hx]
    cases p.pins x <;> simp [hx]

/-- Install a checked parent promotion in the stored pool, leaving membership
unchanged and keeping every unused label isolated. -/
def installPromotion (p : Pool n) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) : Pool n where
  palette := r.palette
  positive := p.positive.trans_le r.palette_bounds.1
  members := p.members
  system := r.system
  pins := r.newPins
  invariant := r.invariant
  pin_bounds := r.pin_bounds
  capacity := p.capacity.trans (Nat.succ_le_succ r.palette_bounds.1)
  outside := by
    intro x hx
    have hxv : x ≠ v := fun h => hx (h ▸ p.free_member hv)
    obtain ⟨hpin, hu⟩ := p.outside x hx
    have hpnew : r.newPins x = some (r.embed (p.system.lower x)) := by
      rw [Promotion.other_pin p.system p.pins v c r hxv, hpin]
      rfl
    have hb := r.pin_bounds x _ hpnew
    constructor
    · exact hpnew.trans (congrArg some hb.1.symm)
    · refine ⟨rfl, hb.2.trans hb.1.symm, ?_, ?_⟩
      · intro y hxy
        rw [r.edges] at hxy
        exact hu.outgoing y hxy
      · intro y hyx
        rw [r.edges] at hyx
        exact hu.incoming y hyx

@[simp] theorem installPromotion_free (p : Pool n) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) :
    (p.installPromotion v hv c r).free = p.free.erase v := by
  ext x
  rw [free_iff, Finset.mem_erase, free_iff]
  change r.newPins x = none ↔ x ≠ v ∧ p.pins x = none
  by_cases hx : x = v
  · subst x
    simp [Promotion.promoted_pin]
  · rw [Promotion.free_preserved p.system p.pins v c r hx]
    simp [hx]

theorem installPromotion_free_card (p : Pool n) (v : Fin n) (hv : p.pins v = none)
    (c : Fin (p.palette + 1)) (r : Promotion.Result p.system p.pins v c) :
    (p.installPromotion v hv c r).free.card + 1 = p.free.card := by
  rw [installPromotion_free]
  exact Finset.card_erase_add_one ((p.free_iff v).mpr hv)

end Pool

/-- The unborn child has two positions and no actual members. -/
def emptySystem (n : ℕ) : WeakSystem (Fin n) 2 where
  edge x y := decide (x = y)
  lower _ := 0
  upper _ := 0

theorem emptySystem_closed (n : ℕ) : (emptySystem n).Closed := by
  constructor
  · intro x
    simp [emptySystem]
  · intro x y z hxy hyz
    simp only [emptySystem, decide_eq_true_eq] at *
    exact hxy.trans hyz

theorem emptySystem_valid_iff (n : ℕ) (f : ColorMap (Fin n) 2) :
    (emptySystem n).Valid f ↔ f = fun _ => 0 := by
  constructor
  · intro hf
    funext x
    exact le_antisymm (hf.1 x).2 (hf.1 x).1
  · rintro rfl
    exact ⟨fun _ => ⟨le_rfl, le_rfl⟩, fun _ _ _ => le_rfl⟩

def emptyPool (n : ℕ) : Pool n where
  palette := 1
  positive := by decide
  members := ∅
  system := emptySystem n
  pins _ := some 0
  invariant := by
    refine ⟨emptySystem_closed n, ?_, ?_, ?_, ?_⟩
    · intro x y hxy _
      exact of_decide_eq_true hxy
    · exact ⟨fun _ => 0, (emptySystem_valid_iff n _).mpr rfl⟩
    · intro f hf x c hx
      have hfc := (emptySystem_valid_iff n f).mp hf
      have hc : c = 0 := (Option.some.inj hx).symm
      simp [hfc, hc]
    · intro x hx
      contradiction
  pin_bounds := by
    intro x d hx
    have hd : d = 0 := (Option.some.inj hx).symm
    simp [emptySystem, hd]
  capacity := by simp
  outside := by
    intro x _
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · intro y hxy
      exact (of_decide_eq_true hxy).symm
    · intro y hyx
      exact of_decide_eq_true hyx

@[simp] theorem emptyPool_count (n : ℕ) : (emptyPool n).system.count = 1 := by
  have hm : (emptySystem n).maps = {fun _ => 0} := by
    ext f
    simp [emptySystem_valid_iff]
  change (emptySystem n).maps.card = 1
  rw [hm, Finset.card_singleton]

@[simp] theorem emptyPool_free (n : ℕ) : (emptyPool n).free = ∅ := by
  simp [Pool.free, emptyPool]

/-- Initially each original label has the whole root palette and only its
reflexive row. For `N+2` labels this gives exactly `(N+2)^(N+2)` maps. -/
def rootSystem (N : ℕ) : WeakSystem (Fin (N + 2)) (N + 1 + 1) where
  edge x y := decide (x = y)
  lower _ := 0
  upper _ := Fin.last (N + 1)

theorem rootSystem_valid (N : ℕ) (f : ColorMap (Fin (N + 2)) (N + 1 + 1)) :
    (rootSystem N).Valid f := by
  constructor
  · intro x
    exact ⟨Fin.zero_le _, Fin.le_last _⟩
  · intro x y hxy
    have heq : x = y := of_decide_eq_true hxy
    simp [heq]

def initialRoot (N : ℕ) : Pool (N + 2) where
  palette := N + 1
  positive := Nat.succ_pos _
  members := Finset.univ
  system := rootSystem N
  pins _ := none
  invariant := by
    refine ⟨?_, ?_, ⟨_, rootSystem_valid N (fun _ => 0)⟩, ?_, ?_⟩
    · constructor
      · intro x
        simp [rootSystem]
      · intro x y z hxy hyz
        have h1 : x = y := of_decide_eq_true hxy
        have h2 : y = z := of_decide_eq_true hyz
        exact decide_eq_true (h1.trans h2)
    · intro x y hxy _
      exact of_decide_eq_true hxy
    · intro f hf x c hx
      contradiction
    · intro x _
      have hl := ((rootSystem N).valid_between_windows _ (rootSystem_valid N (fun _ => 0)) x).1
      have hu := ((rootSystem N).valid_between_windows _
        (rootSystem_valid N (fun _ => Fin.last (N + 1))) x).2
      exact hl.trans_lt ((show (0 : Fin (N + 1 + 1)) < Fin.last (N + 1) from
        Nat.succ_pos N).trans_le hu)
  pin_bounds := by intro x d hx; contradiction
  capacity := by simp
  outside := by intro x hx; exact (hx (Finset.mem_univ x)).elim

@[simp] theorem initialRoot_count (N : ℕ) :
    (initialRoot N).system.count = (N + 2) ^ (N + 2) := by
  have hm : (rootSystem N).maps = Finset.univ := by
    ext f
    simp [rootSystem_valid]
  change (rootSystem N).maps.card = _
  rw [hm]
  simp [Nat.add_assoc]

@[simp] theorem initialRoot_free (N : ℕ) : (initialRoot N).free = Finset.univ := by
  ext v
  rw [Pool.free_iff]
  simp [initialRoot]

end SortingAdversary.Optimal.PoolState
