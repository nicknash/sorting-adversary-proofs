import SortingAdversary.Continuous.PolylogCompareComplexity
import SortingAdversary.Continuous.PolylogCompareProofs

/-!
# Charging the actual branches of an online comparison

A profiling pass follows the chosen trials and the reserved repair path.
Only a failed selection incurs a prefix write; only a reserved coordinate
runs its central test. The comparison itself supplies every intermediate
memory used to look up physical costs.
-/
namespace SortingAdversary.Continuous.PolylogProfileCompare

open PolylogCompare
open PolylogAdversary (parameter extra)
open Controller (Ready Admissible totalDepth horizon)
open Optimal.Parameters (logCap)
attribute [local instance] PolylogOracle.choices PolylogOracle.choices_valid

/-- Additional costs for the stored operations, measured at their actual arguments. -/
structure Charges (n : ℕ) where
  test : ScheduledMemory n → Query n → ℕ
  write : ScheduledMemory n → Fin n → Option ℚ → ℕ
  central : ScheduledMemory n → Fin n → ℕ
  refine : (m : ScheduledMemory n) → Fin n → WriteResult m → ℕ
  record : ScheduledMemory n → Query n → Answer → ℕ

variable {n : ℕ}
local notation "D" => binaryPoint n
local notation "k" => parameter n

def selectCharges (rates : Charges n) (q : Query n) : ℕ → ScheduledMemory n → ℕ
  | 0, _ => 0
  | f+1, m =>
    match (check D k m q).value with
    | .answer _ => rates.test m q
    | .refine x =>
      let v := writePrefix D m x
      rates.test m q + rates.write m x none + rates.refine m x v +
        selectCharges rates q f (move k m x v).value

def repairCharges (rates : Charges n) : List (Fin n) → ScheduledMemory n → ℕ
  | [], _ => 0
  | x::xs, m =>
    let q := (candidate D k m x).value
    let v := mint D m x q
    rates.central m x + rates.write m x q + rates.refine m x v +
      repairCharges rates xs (repairMove D k m x).value

def compareCharges (rates : Charges n) (m : ScheduledMemory n) (q : Query n) : ℕ :=
  let s := selectCharges rates q 3 m
  match (select D k q 3 m).value with
  | none => s
  | some (u,a) =>
    let z := (record k u q a).value
    let xs := (PolylogRepair.choose z.1.spatial.graph k z.2).value
    s + rates.record u q a + repairCharges rates xs z.1

/-- Uniform charges at the intermediate states actually visited. Mutations
use their original work as a majorant because their pointwise comparisons
are expanded into priced balanced-map paths. -/
structure Bounded (rates : Charges n) (B F : ℕ) : Prop where
  test : ∀ m M, Tracks m M → Ready k M → totalDepth M ≤ depthLimit n → ∀ q,
    rates.test m q ≤ B
  selection : ∀ m M, Tracks m M → Ready k M → totalDepth M ≤ depthLimit n → ∀ x,
    let v := writePrefix D m x
    rates.write m x none + rates.refine m x v ≤ B+F*(move k m x v).work
  central : ∀ m M, Tracks m M → Admissible k M → totalDepth M ≤ depthLimit n → ∀ x,
    let q := (candidate D k m x).value
    let v := mint D m x q
    rates.central m x + rates.write m x q + rates.refine m x v ≤
      2*B+F*(repairMove D k m x).work
  record : ∀ m M, Tracks m M → Ready k M → totalDepth M ≤ depthLimit n → ∀ q a,
    rates.record m q a ≤ F*(PolylogCompare.record k m q a).work

private theorem select_bound {rates : Charges n} {B F : ℕ} (p : Bounded rates B F)
    (hk : 64 ≤ k) (q : Query n) (f : ℕ) (m : ScheduledMemory n) (M : Controller.Memory n)
    (hm : Tracks m M) (ready : Ready k M) (room : totalDepth M + f ≤ depthLimit n) :
    selectCharges rates q f m ≤ f*(2*B)+F*(select D k q f m).work := by
  induction f generalizing m M with
  | zero => simp [selectCharges]
  | succ f ih =>
    have curr : totalDepth M ≤ depthLimit n := by omega
    have c₁ := p.test m M hm ready curr q
    obtain ⟨_,rep⟩ := hm.storage
    have eq := check_value extra rep hk ready.admissible (Nat.lt_size_self _) (binaryPoint_short n) q
    change (check D k m q).value.realize M = PolylogOracle.attempt M k q at eq
    cases ev : (check D k m q).value with
    | answer a =>
      simp only [selectCharges,select,ev,Nat.succ_mul]
      omega
    | refine x =>
      let c := PolylogOracle.prefixAnchor M x
      let v := writePrefix D m x
      let r := move k m x v
      let N := Controller.applyMove M (Controller.makeMove M x c)
      have part : PolylogOracle.attempt M k q = .refine x c := by
        simpa only [ev,PolylogActive.Decision.realize,c] using eq.symm
      have hm' : Tracks r.value N := select_step_aligned hk q m M hm ready curr x part
      have ready' := Controller.attempt_refine_ready M k hk ready q x c part
      have depth : totalDepth N = totalDepth M+1 := Controller.totalDepth_applyMove ..
      have tail := ih r.value N hm' ready' (by omega)
      rw [Nat.mul_left_comm f 2 B] at tail
      have moved := p.selection m M hm ready curr x
      change rates.write m x none + rates.refine m x v ≤ B+F*r.work at moved
      simp only [selectCharges,select,ev,Nat.succ_mul]
      change rates.test m q + rates.write m x none+rates.refine m x v + selectCharges rates q f r.value ≤
        _+F*((check D k m q).work+r.work+(select D k q f r.value).work+3)
      simp only [Nat.mul_add]
      omega

private theorem repair_bound {rates : Charges n} {B F : ℕ} (p : Bounded rates B F)
    (hk : 64 ≤ k) (xs : List (Fin n)) (m : ScheduledMemory n) (M : Controller.Memory n)
    (hm : Tracks m M) (adm : Admissible k M) (room : totalDepth M+xs.length ≤ depthLimit n) :
    repairCharges rates xs m ≤ xs.length*(2*B)+F*(repairList D k xs m).work := by
  induction xs generalizing m M with
  | nil => simp [repairCharges]
  | cons x xs ih =>
    have curr : totalDepth M ≤ depthLimit n := by simp only [List.length_cons] at room; omega
    obtain ⟨_,rep⟩ := hm.storage
    have eq := candidate_value extra rep hk adm (Nat.lt_size_self _) (binaryPoint_short n) x
    let N := Controller.applyMove M (Controller.makeMove M x (PolylogOracle.anchor M k x))
    let r := repairMove D k m x
    have hm' : Tracks r.value N := repair_step_aligned hk m M hm adm curr x eq
    have adm' := (PolylogOracle.anchor_move_spec M k hk adm x).2.2.2.1
    have depth : totalDepth N = totalDepth M+1 := Controller.totalDepth_applyMove ..
    have tail := ih r.value N hm' adm' (by simp only [List.length_cons] at room; omega)
    rw [Nat.mul_left_comm xs.length 2 B] at tail
    have here := p.central m M hm adm curr x
    change _ ≤ 2*B+F*r.work at here
    simp only [repairCharges,repairList,List.length_cons,Nat.succ_mul]
    change _+repairCharges rates xs r.value ≤ _+F*(r.work+(repairList D k xs r.value).work+2)
    simp only [Nat.mul_add]
    omega

theorem compareCharges_le {rates : Charges n} {B F : ℕ} (p : Bounded rates B F)
    (hk : 64 ≤ k) (m : ScheduledMemory n) (M : Controller.Memory n) (hm : Tracks m M)
    (ready : Ready k M) (depth : totalDepth M ≤ horizon n) (q : Query n) :
    compareCharges rates m q ≤ (2^k+3)*(2*B)+F*(PolylogCompare.compare D k m q).work := by
  have hp : 0 < 2^k := by positivity
  have room : totalDepth M+3 ≤ depthLimit n := by unfold depthLimit; omega
  have sc := select_bound p hk q 3 m M hm ready room
  obtain ⟨s,hs⟩ := Controller.selectLoop_total k hk q M ready
  obtain ⟨u,hu,align,depth'⟩ := select_simulates Tracks (B := depthLimit n) hk q
    (fun y N ht ha _ => by
      obtain ⟨_,r⟩ := ht.storage
      exact check_value extra r hk ha.admissible (Nat.lt_size_self _) (binaryPoint_short n) q)
    (select_step_aligned hk q) 3 m M hm ready (by omega) hs
  have sel := Controller.selectLoop_spec k hk q 3 M ready s hs
  have mass := PolylogOracle.attempt_answer_probability s.memory k (by omega) sel.1.toGeometric q s.answer sel.2.1
  let N := Controller.recorded s.memory q s.answer
  have post : Admissible k N := sel.1.recordedAdmissible q s.answer
    (sel.1.toGeometric.recorded hk q s.answer mass.1 mass.2)
  let z := record k u q s.answer
  let path := PolylogRepair.choose z.value.1.spatial.graph k z.value.2
  have stored : Tracks z.value.1 N := record_aligned align sel.1 (PolylogResources.label_fits n) q s.answer post
  have eq : path.value = PolylogRepair.reserved N.tree.system.edge k :=
    record_choose_aligned align sel.1 (PolylogResources.label_fits n) q s.answer post
  have length : path.value.length ≤ 2^k := eq ▸ reserved_length N k
  have rd : totalDepth N = totalDepth s.memory := rfl
  have cap : totalDepth N+path.value.length ≤ depthLimit n := by unfold depthLimit; omega
  have pc := repair_bound p hk path.value z.value.1 N stored post cap
  have rc := p.record u s.memory align sel.1 (by omega) q s.answer
  change _ ≤ F*z.work at rc
  have count := Nat.mul_le_mul_right (2*B) length
  change (select D k q 3 m).value = some (u,s.answer) at hu
  simp only [compareCharges,PolylogCompare.compare,hu]
  change selectCharges rates q 3 m + rates.record u q s.answer + repairCharges rates path.value z.value.1 ≤
    (2^k+3)*(2*B)+F*((select D k q 3 m).work+z.work+path.work+(repairList D k path.value z.value.1).work+4)
  simp only [Nat.add_mul,Nat.mul_add]
  omega

end SortingAdversary.Continuous.PolylogProfileCompare
