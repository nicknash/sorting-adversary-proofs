import SortingAdversary.Continuous.PolylogExecution
import SortingAdversary.Continuous.StageWork
import SortingAdversary.Continuous.PolylogPreparedDefs
import SortingAdversary.Continuous.PolylogAdversary
import SortingAdversary.Continuous.PolylogMemory
import SortingAdversary.Continuous.PolylogResources
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Uniform startup of the sparse adversary

Compute the logarithmic cap, run the capped stage scan and materialize the
selected constants once. The rounded sweep count is computed by an integer
ceiling logarithm after the exact moment search. Persistent tables share the
two children of every initial branch.
-/

namespace SortingAdversary.Continuous.PolylogStartup

open Optimal
open Optimal.PrimitiveWork (Result)
open Optimal.Parameters (logCap)
open UniformStages ArbitraryLabels EnclosureParameters PolylogPrepared
open PolylogBits

private abbrev recipe := PolylogSchedule.recipe PolylogAdversary.extra

/-- The fixed coefficient is independent of the input. -/
theorem logPower_linear (n p : ℕ) :
    (logCap n + 1)^p ≤ (p.factorial * 2^p) * (n+1) := by
  let A := logCap n
  calc
    (A+1)^p ≤ (A+1).ascFactorial p := Nat.pow_succ_le_ascFactorial _ _
    _ = p.factorial * (A+p).choose p := Nat.ascFactorial_eq_factorial_mul_choose _ _
    _ ≤ p.factorial * (2^(A+p)) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = (p.factorial * 2^p) * 2^A := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (Nat.succ_ne_zero n))

private theorem stage_fit {n : ℕ} (hk : 64 ≤ PolylogAdversary.parameter n) :
    Recipe.budget.need (PolylogSchedule.stage PolylogAdversary.extra n) ≤ logCap n := by
  have h := CappedStageScan.stage_need recipe n (PolylogSchedule.active_stage hk)
  exact (max_le_iff.mp (max_le_iff.mp h).1).2

/-- Formula for the least *positive* sweep count at half width. -/
theorem sweeps_integer {k : ℕ} (hk : 0 < k) :
    Neighborhood.sweeps k (pathHeight k) hk (halfWidth k) (width_pos k) =
      max 1 (Nat.clog 2 (2*failureDen k * (2*accuracyDen k)^momentPower k (pathHeight k))) := by
  let H := pathHeight k
  let T := 2*failureDen k * (2*accuracyDen k)^momentPower k H
  have den : CertificateSuccess.accuracy k (neighborhoodBound k H) (halfWidth k) =
      1 / ((2 * accuracyDen k : ℕ) : ℚ) := by
    rw [PolylogEnclosure.accuracy_half, UniformStages.accuracy_eq]
    push_cast; ring
  have test (t : ℕ) : (1 / 2 : ℚ)^t ≤ CertificateSuccess.failure k *
      CertificateSuccess.accuracy k (neighborhoodBound k H) (halfWidth k) ^ momentPower k H / 2 ↔
      Nat.clog 2 T ≤ t := by
    rw [den,UniformStages.failure_eq,StageArithmetic.sweep_test_iff _ _ _ _
      (failureDen_pos hk) (Nat.mul_pos (by decide) (accuracyDen_pos hk))]
    exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).symm
  unfold Neighborhood.sweeps sweepCount
  apply le_antisymm
  · apply Nat.find_min'; exact ⟨by omega, (test _).2 (le_max_right ..)⟩
  · have e := Nat.find_spec (sweepCount_exists k H _ _ (CertificateSuccess.accuracy_pos hk (neighborhoodBound k H) (width_pos k))
      (CertificateSuccess.failure_pos hk))
    exact max_le e.1 ((test _).1 e.2)

theorem grid_integer (k : ℕ) : PolylogOracle.grid k = Nat.clog 2 (4 * accuracyDen k) := by
  unfold PolylogOracle.grid PolylogEnclosure.gridBits
  rw [UniformStages.accuracy_eq]
  have e : (4:ℚ) / (1 / (accuracyDen k : ℚ)) = ((4 * accuracyDen k : ℕ) : ℚ) := by
    push_cast; simp [div_eq_mul_inv]
  rw [e,Nat.ceil_natCast]

/-- Calibration uses the counted moment search, repeated multiplication for
the remaining power, and division-by-two loops for both logarithms. -/
def parameters (k H : ℕ) : Result Params :=
  let m := StageWork.moment k H
  let a := StageWork.accuracyDen k
  let power := StageWork.power (2*a.value) m.value
  let sweeps := RoundingWork.clogTwo (2 * (200*k) * power.value)
  let grid := RoundingWork.clogTwo (4*a.value)
  let exponent := StageWork.exponent k H
  ⟨⟨k,H,max 1 sweeps.value,grid.value,exponent.value⟩,
    m.work+a.work+power.work+sweeps.work+grid.work+exponent.work+12⟩

theorem parameters_value {k : ℕ} (hk : 0 < k) :
    (parameters k (pathHeight k)).value = Params.stage k := by
  simp only [parameters, StageWork.accuracyDen_value,StageWork.moment_value,StageWork.power_value,
    RoundingWork.clogTwo_value,StageWork.exponent_value,Params.stage,dif_pos hk,
    sweeps_integer hk,grid_integer,failureDen]

theorem parameters_work {n : ℕ} (hk : 64 ≤ PolylogAdversary.parameter n) :
    let k := PolylogAdversary.parameter n
    (parameters k (pathHeight k)).work ≤ 200*(logCap n+1)^2 := by
  let k := PolylogAdversary.parameter n
  let A := logCap n
  let H := pathHeight k
  have pos : 0 < k := by dsimp [k]; omega
  obtain ⟨ck,ch,cb,ce,_,cp,_,ca,_⟩ := admitted_scalar_bounds _ _ (stage_fit hk)
  have hm := StageWork.moment_work k H A ch ce cp
  have ha := StageWork.accuracyDen_work k A ck ch cb
  have hr := CappedStageScan.stage_need recipe n (PolylogSchedule.active_stage hk)
  let j := PolylogSchedule.stage PolylogAdversary.extra n
  have hs : PolylogSchedule.roundedSweeps.need j ≤ A := by
    change max (max (PolylogSchedule.shortPrecision.need j) _) _ ≤ A at hr
    have hE := (max_le_iff.mp (max_le_iff.mp hr).1).1
    change max _ (max (PolylogSchedule.roundedEnumeration.need j) _) ≤ _ at hE
    have hP := (max_le_iff.mp (max_le_iff.mp hE).2).1
    change max _ (max (max _ (max (PolylogSchedule.roundedSweeps.need j) _)) _) ≤ _ at hP
    exact (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hP).2).1).2).1
  have ht : 2 * failureDen k * (2*accuracyDen k)^momentPower k H ≤ A := by
    apply le_trans _ ((PolylogSchedule.roundedSweeps.value_le_need j).trans hs)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right
      (Nat.mul_pos (by decide) (accuracyDen_pos pos)) (ParameterBounds.momentPower_le_envelope k H))
  have st := Nat.clog_le_of_le_pow (b := 2) (Nat.lt_two_pow_self (n :=
    2*failureDen k*(2*accuracyDen k)^momentPower k H)).le
  have sg := Nat.clog_le_of_le_pow (b := 2) (Nat.lt_two_pow_self (n := 4*accuracyDen k)).le
  change k ≤ A at ck
  change H ≤ A at ch
  change alphabetExponent k H ≤ A at ce
  change momentPower k H ≤ A at cp
  change accuracyDen k ≤ A at ca
  change (parameters k H).work ≤ 200*(A+1)^2
  simp only [parameters,StageWork.power_work,StageWork.moment_value,StageWork.accuracyDen_value,
    RoundingWork.clogTwo_work,StageWork.power_value,StageWork.exponent_work]
  unfold failureDen at st ht
  nlinarith

/-- Every multiplication in the exact moment test, including the failed
tests, has logarithmic bit length in the input size. The admission recipe
includes an exponential in the moment envelope itself. -/
theorem moment_word_bits {n : ℕ} (hk : 64 ≤ PolylogAdversary.parameter n) (i : ℕ)
    (hi : i ≤ momentPower (PolylogAdversary.parameter n) (pathHeight (PolylogAdversary.parameter n))) :
    let k := PolylogAdversary.parameter n
    let H := pathHeight k
    let base := alphabet k H ^ H
    (base ^ i).size ≤ 10*(logCap n+1) ∧
      (4 * neighborhoodBound k H * (base-1)^i).size ≤ 10*(logCap n+1) := by
  let k := PolylogAdversary.parameter n
  let H := pathHeight k
  let m := ParameterBounds.momentEnvelope k H
  let B := alphabet k H ^ H
  let A := logCap n
  let M := neighborhoodBound k H
  have kp : 0 < k := by dsimp [k]; omega
  have mp : 0 < M := neighborhoodBound_pos ..
  have bP : 0 < ParameterBounds.alphabetBound k H := by unfold ParameterBounds.alphabetBound; positivity
  have bm : B ≤ m := (Nat.pow_le_pow_left (ParameterBounds.alphabet_le k H) H).trans
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) mp))
  have cm : 4*M ≤ m := Nat.le_mul_of_pos_right _ (pow_pos bP _)
  have pi : i ≤ m := hi.trans (ParameterBounds.momentPower_le_envelope ..)
  have hs := (Recipe.sweeps.value_le_need _).trans ((Recipe.sweeps_need _).trans (stage_fit hk))
  change 2*failureDen k*(accuracyDen k)^m ≤ A at hs
  have ad : 2 ≤ accuracyDen k := by
    have _ := Nat.two_pow_pos (2*k*M)
    change 2 ≤ 800*k*(M+1)*2^(2*k*M)
    exact (show 2 ≤ 800*k*(M+1) by nlinarith).trans (Nat.le_mul_of_pos_right _ ‹0 < 2^(2*k*M)›)
  have em : 2^m ≤ A := (Nat.pow_le_pow_left ad m).trans <|
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) (failureDen_pos kp))).trans hs
  have square : (m+1)^2 ≤ 8*A := calc
    _ ≤ (m+1).ascFactorial 2 := Nat.pow_succ_le_ascFactorial _ _
    _ = 2 * (m+2).choose 2 := Nat.ascFactorial_eq_factorial_mul_choose ..
    _ ≤ 2 * 2^(m+2) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow ..)
    _ = 8 * 2^m := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ em
  have bp : B^i ≤ 2^(m^2) := calc
    _ ≤ (2^m)^m := (Nat.pow_le_pow_left (bm.trans Nat.lt_two_pow_self.le) _).trans (Nat.pow_le_pow_right (by positivity) pi)
    _ = _ := by rw [← pow_mul,pow_two]
  have low : 4*M*(B-1)^i ≤ 2^(m+m^2) := by
    rw [pow_add]
    exact Nat.mul_le_mul (cm.trans Nat.lt_two_pow_self.le)
      ((Nat.pow_le_pow_left (Nat.sub_le _ _) _).trans bp)
  have hh := Nat.size_le_size bp
  have ll := Nat.size_le_size low
  simp only [Nat.size_pow] at hh ll
  change (B^i).size ≤ 10*(A+1) ∧ (4*M*(B-1)^i).size ≤ 10*(A+1)
  constructor <;> nlinarith

/-- One intern in `initializeCache` is a forward lookup and at most two
tree inserts. The array copy allowance covers a non-in-place push. -/
theorem cache_level_work (S : Store) (d : ℕ) :
    let prev := initializeCache S d
    let z := prev.cache.lookup d false
    let o := prev.cache.lookup d true
    let kz : Key := (d+1,z,z)
    let ko : Key := (d+1,o,o)
    PolylogDictionary.internComparisons prev.heap kz +
      PolylogDictionary.internComparisons (prev.heap.intern kz).1 ko + prev.table.size + 12 ≤
        50*(d+2) := by
  dsimp only
  let prev := initializeCache S d
  let kz : Key := (d+1, prev.cache.lookup d false, prev.cache.lookup d false)
  let ko : Key := (d+1, prev.cache.lookup d true, prev.cache.lookup d true)
  have h := PolylogDictionary.internComparisons_allocated prev.heap prev.valid kz
  have j := PolylogDictionary.internComparisons_allocated (prev.heap.intern kz).1
    (prev.heap.intern_valid prev.valid kz) ko
  have := Nat.log2_le_self prev.heap.next
  have := Nat.log2_le_self (prev.heap.intern kz).1.next
  have := prev.allocated
  have := (prev.heap.intern_growth prev.valid kz).1
  have := prev.size
  change PolylogDictionary.internComparisons prev.heap kz +
    PolylogDictionary.internComparisons (prev.heap.intern kz).1 ko + prev.table.size + 12 ≤ _
  omega

/-- The summed level charges include interning both uniform roots, reading
their old addresses, and writing the next cache entry. -/
def cacheWork : ℕ → ℕ
  | 0 => 4
  | d+1 => cacheWork d + 50*(d+2)

theorem cache_work (b : ℕ) : cacheWork b ≤ 50*(b+1)^2 := by
  induction b with
  | zero => decide
  | succ b ih => simp only [cacheWork]; nlinarith

/-- A single set bit needs one new branch per position on its path.
All siblings are the appropriate cached zero. -/
def single (cache : ℕ → Bool → ℕ) (H : Heap) : {h : ℕ} → Position h → Result PolylogRawBits.Output
  | _, .here => ⟨⟨H,1⟩,1⟩
  | _, @Position.low d p =>
    let t := single cache H p
    let k : Key := (d+1,cache d false,t.value.addr)
    let w := t.value.heap.intern k
    ⟨⟨w.1,w.2⟩,t.work+PolylogDictionary.internComparisons t.value.heap k+6⟩
  | _, @Position.high d p =>
    let t := single cache H p
    let k : Key := (d+1,t.value.addr,cache d false)
    let w := t.value.heap.intern k
    ⟨⟨w.1,w.2⟩,t.work+PolylogDictionary.internComparisons t.value.heap k+6⟩

theorem single_work {H : Heap} (v : H.Valid) (cache : ℕ → Bool → ℕ) {h : ℕ} (p : Position h) :
    let t := single cache H p
    t.value.heap.Valid ∧ t.value.heap.next ≤ H.next+h ∧
      t.work ≤ 1+h*(9*(H.next+h+1)+6) := by
  induction p with
  | here => exact ⟨v,by simp [single],by simp [single]⟩
  | high p ih | low p ih =>
    obtain ⟨valid,alloc,work⟩ := ih
    simp only [single]
    refine ⟨Heap.intern_valid _ valid _, ?_, ?_⟩
    · exact ((Heap.intern_growth _ valid _).1).trans (by omega)
    · generalize keyEq : (_,_,_) = key
      have hj := PolylogDictionary.internComparisons_allocated _ valid key
      have := Nat.log2_le_self (single cache H p).value.heap.next
      nlinarith

theorem single_eq {S : Store} {H : Heap} (v : H.Valid) {b h} (c : Cached S H b) (p : Position h)
    (fit : h ≤ b) :
    PolylogRawBits.addUnit c.lookup H p (c.lookup h false) =
      ((single c.lookup H p).value,false) := by
  induction p with
  | here =>
    have z := c.spec fit false
    have eq := (z.same_iff v (Represents.leaf (S := S) (H := H) false)).2 rfl
    simp [PolylogRawBits.addUnit, single,eq]
  | @high d p ih | @low d p ih =>
    have hd : d ≤ b := by omega
    let u := c.cell fit false
    have left : (H.children (c.lookup (d+1) false)).1 = c.lookup d false := by
      apply (u.left.rep.same_iff v (c.spec hd false)).2
      simp [filled,S.split_join]
    have right : (H.children (c.lookup (d+1) false)).2 = c.lookup d false := by
      apply (u.right.rep.same_iff v (c.spec hd false)).2
      simp [filled,S.split_join]
    simp only [PolylogRawBits.addUnit,left,right,ih hd,Bool.false_eq_true,if_false]
    rfl

/-- Count one branch allocation per height. Both pointers refer to that
same recursive result. -/
def fill (x : α) : (t : ℕ) → Result (PolylogRouting.Table α t)
  | 0 => ⟨.leaf x,1⟩
  | t+1 => let child := fill x t; ⟨.node child.value child.value,child.work+2⟩

@[simp] theorem fill_value (x : α) (t : ℕ) : (fill x t).value = PolylogRouting.Table.fill x t := by
  induction t <;> simp_all [fill,PolylogRouting.Table.fill]

@[simp] theorem fill_work (x : α) (t : ℕ) : (fill x t).work = 2*t+1 := by
  induction t <;> simp_all [fill]
  omega

def spatial (n t z o : ℕ) : Result (PolylogStorage.State n t) :=
  let pred := fill ([] : List (Fin n)) t
  let succ := fill ([] : List (Fin n)) t
  let lower := fill z t
  let upper := fill o t
  let child := fill (none : Option (PolylogHierarchy.Cursor t)) t
  let dir := fill child.value t
  let ancestors := fill (⟨0,0⟩ : PolylogRouting.Entry ℕ) t
  let loc := fill (⟨0,⟨0,ancestors.value⟩⟩ : PolylogHierarchy.Cursor t) t
  ⟨⟨⟨pred.value,succ.value⟩,⟨lower.value,upper.value⟩,⟨1,dir.value⟩,loc.value⟩,
    pred.work+succ.work+lower.work+upper.work+child.work+dir.work+ancestors.work+loc.work+8⟩

@[simp] theorem spatial_value (n t z o : ℕ) :
    (spatial n t z o).value = PolylogStorage.initial n t z o := by
  simp only [spatial,fill_value]; rfl

@[simp] theorem spatial_work (n t z o : ℕ) : (spatial n t z o).work = 16*(t+1) := by
  simp only [spatial,fill_work]; ring

private theorem single_embed (D b : ℕ) :
    let base := initializeCache blockStore b
    let w := PolylogEmbed.embedAddr D 0 1 base.valid base.cache (le_refl b)
    (single base.cache.lookup base.heap (atBit b D)).value = PolylogRawBits.erase w.toWrite := by
  dsimp only
  let base := initializeCache blockStore b
  exact congrArg Prod.fst (single_eq base.valid base.cache (atBit b D) (le_refl b)).symm

/-- Ground-state construction with a charged single-bit write at the binary
point. Its heap and roots agree literally with the general embedding. -/
def memory (n t b D : ℕ) : Result (PolylogCompare.Memory n t b) :=
  let base := initializeCache blockStore b
  let one := single base.cache.lookup base.heap (atBit b D)
  let z := base.cache.lookup b false
  let state := spatial n t z one.value.addr
  let w := PolylogEmbed.embedAddr D 0 1 base.valid base.cache (le_refl b)
  have eq := single_embed D b
  have heapEq : one.value.heap = w.heap := congrArg PolylogRawBits.Output.heap eq
  ⟨⟨state.value,one.value.heap,heapEq ▸ w.valid,heapEq ▸ w.growth.typed base.typed,
      ⟨base.cache.lookup, by rw [heapEq]; exact (base.cache.lift w.growth).spec⟩,z,one.value.addr⟩,
    cacheWork b+one.work+4*b+state.work+9⟩

private theorem memory_ext {a b : PolylogCompare.Memory n t h}
    (s : a.spatial = b.spatial) (e : a.heap = b.heap) (l : a.cache.lookup = b.cache.lookup)
    (z : a.zero = b.zero) (o : a.one = b.one) : a = b := by
  cases a with | mk sa ha va ta ca za oa =>
    cases b with | mk sb hb vb tb cb zb ob =>
      dsimp only at *
      subst sb; subst hb; subst zb; subst ob
      cases ca; cases cb
      congr

theorem memory_value (n t b D : ℕ) :
    (memory n t b D).value = PolylogCompare.initialMemory n t b D := by
  apply memory_ext
  · simp only [memory, PolylogCompare.initialMemory, spatial_value,single_embed]; rfl
  · exact congrArg PolylogRawBits.Output.heap (single_embed D b)
  · rfl
  · rfl
  · exact congrArg PolylogRawBits.Output.addr (single_embed D b)

theorem memory_work (n t b D : ℕ) :
    (memory n t b D).work ≤ 100*(b+1)^2+16*(t+1)+10 := by
  let base := initializeCache blockStore b
  have h := (single_work base.valid base.cache.lookup (atBit b D)).2.2
  have bnd := base.allocated
  have cc := cache_work b
  simp only [memory,spatial_work]
  change cacheWork b + (single base.cache.lookup base.heap (atBit b D)).work + 4*b +
    16*(t+1)+9 ≤ _
  nlinarith [Nat.mul_le_mul_left b bnd]

/-- The bit length is computed by successive halvings. -/
def bits (x : ℕ) : Result ℕ :=
  if x = 0 then ⟨0,1⟩ else
    let l := StateWork.logTwo x
    ⟨l.value+1,l.work+2⟩

@[simp] theorem bits_value (x : ℕ) : (bits x).value = x.size := by
  by_cases hx : x = 0
  · simp [bits,hx]
  simp only [bits, if_neg hx, StateWork.logTwo_value]
  apply le_antisymm
  · exact Nat.lt_size.mpr (Nat.pow_log_le_self 2 hx)
  · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide) _)

theorem bits_work (x : ℕ) : (bits x).work ≤ 3*x.size+3 := by
  by_cases hx : x = 0
  · simp [bits,hx]
  have h := Nat.lt_size.mpr (Nat.pow_log_le_self 2 hx)
  simp only [bits, if_neg hx, StateWork.logTwo_work]
  omega

private theorem inactive {n : ℕ} (h : ¬ 64 ≤ PolylogAdversary.parameter n) :
    PolylogAdversary.parameter n = 32 := by
  let j := PolylogSchedule.stage PolylogAdversary.extra n
  have jz : j = 0 := by
    by_contra hh
    exact h (degree_ge_sixtyFour j (Nat.pos_of_ne_zero hh))
  change degree j = 32
  rw [jz]; decide

private theorem capacity_size (n : ℕ) :
    (PolylogSchedule.capacity (logCap n) (pathHeight (PolylogAdversary.parameter n)) n).size ≤
      40+3*(logCap n+1) := by
  by_cases h : 64 ≤ PolylogAdversary.parameter n
  · apply (PolylogSchedule.capacity_bits h (le_refl (logCap n))).trans; omega
  rw [inactive h]
  let A := logCap n
  have hh : Controller.horizon n ≤ n*n := Nat.mul_le_mul_left n
    (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le)
  have ha : A ≤ n := Parameters.logCap_le_input n
  have D : PolylogSchedule.capacity A (pathHeight 32) n ≤ 2^36*(n+1)^3 := by
    unfold PolylogSchedule.capacity
    have c : pathHeight 32 = 8589934592 := by decide
    rw [c]; norm_num; nlinarith [Nat.zero_le (n^3)]
  apply Nat.size_le.mpr
  have np : n+1 ≤ 2^(A+1) := (Nat.lt_pow_succ_log_self (by decide) _).le
  calc
    _ ≤ 2^36*(2^(A+1))^3 := D.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left np 3))
    _ < 2^(40+3*(A+1)) := by
      rw [Nat.mul_comm 3, pow_add 2 40, pow_mul 2 (A+1)]
      exact Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)

private def stageData (k H : ℕ) : Result Params :=
  if 64 ≤ k then parameters k H else ⟨⟨k,0,0,0,0⟩,1⟩

private theorem stageData_value (k : ℕ) : (stageData k (pathHeight k)).value =
    if 64 ≤ k then Params.stage k else ⟨k,0,0,0,0⟩ := by
  by_cases h : 64 ≤ k
  · simp [stageData,h,parameters_value (show 0 < k by omega)]
  · simp [stageData,h]

private theorem stageData_work (n : ℕ) :
    let k := PolylogAdversary.parameter n
    (stageData k (pathHeight k)).work ≤ 200*(logCap n+1)^2 := by
  dsimp only
  by_cases h : 64 ≤ PolylogAdversary.parameter n
  · simpa only [stageData,if_pos h] using parameters_work h
  · simp only [stageData,if_neg h]
    exact Nat.mul_pos (by decide) (pow_pos (Nat.succ_pos _) _)

/-- The cutoff, depth and selected tuple are shared by their consumers.
The inactive branch omits the moment search. -/
def scalars (n : ℕ) : Result (PolylogExecution.Config × ℕ) :=
  let cap := StateWork.logTwo (n+1)
  let chosen := CappedStageScan.scan recipe cap.value 0 cap.value
  let k := StateWork.powTwo (chosen.stage+5)
  let depth := StateWork.powTwo k.value
  let H := depth.value * 2
  let clock := RoundingWork.clogTwo n
  let Q := n*clock.value
  let D := cap.value + 2*(Q+1)*(H+2)+8
  let b := bits D
  let P := stageData k.value H
  ⟨(⟨k.value,depth.value,D,13+6*(cap.value+1),b.value,P.value⟩,Q),
    cap.work+chosen.work+k.work+depth.work+clock.work+b.work+P.work+19⟩

theorem scalars_value (n : ℕ) :
    (scalars n).value = (PolylogExecution.config n,Controller.horizon n) := by
  simp only [scalars,StateWork.logTwo_value,StateWork.powTwo_value,RoundingWork.clogTwo_value,bits_value]
  change ((⟨PolylogAdversary.parameter n,_,_,_,_,
      (stageData (PolylogAdversary.parameter n) (pathHeight (PolylogAdversary.parameter n))).value⟩ : PolylogExecution.Config),_) = _
  rw [stageData_value]; rfl

theorem scalars_work (n : ℕ) : (scalars n).work ≤
    (27*recipe.nodes+1)*(n+1) + 1000*(logCap n+1)^2 := by
  let k := PolylogAdversary.parameter n
  let A := logCap n
  let j := PolylogSchedule.stage PolylogAdversary.extra n
  let Q := Controller.horizon n
  let D := PolylogSchedule.capacity A (pathHeight k) n
  have hs := PolylogSchedule.selection_work_linear PolylogAdversary.extra n
  have hj : j ≤ A := CappedStageScan.stage_le recipe n
  have hk : k ≤ A+32 := by
    by_cases h : 64 ≤ PolylogAdversary.parameter n
    · exact (admitted_scalar_bounds _ _ (stage_fit h)).1.trans (Nat.le_add_right _ _)
    · simp [k,inactive h]
  have hc : Nat.clog 2 n ≤ A+1 := Nat.clog_le_of_le_pow <|
    (Nat.le_succ n).trans (Nat.lt_pow_succ_log_self (by decide) _).le
  have hb := bits_work D
  have db : D.size ≤ 40+3*(A+1) := capacity_size n
  have hp : (stageData k (pathHeight k)).work ≤ 200*(A+1)^2 := stageData_work n
  simp only [scalars,StateWork.logTwo_value,StateWork.logTwo_work,StateWork.powTwo_value,
    StateWork.powTwo_work,RoundingWork.clogTwo_value,RoundingWork.clogTwo_work]
  change 3*A+1 + (CappedStageScan.select recipe n).work + (2*(j+5)+1) + (2*k+1) +
    (4*Nat.clog 2 n+1) + (bits D).work + (stageData k (pathHeight k)).work + 19 ≤ _
  change (CappedStageScan.select recipe n).work ≤ (27*recipe.nodes+1)*(n+1) at hs
  change _ ≤ _ + 1000*(A+1)^2
  nlinarith

private def boot (n : ℕ) (s : PolylogExecution.Config × ℕ) :
    Result (Σ c, PolylogExecution.State n c) :=
  let c := s.1
  if 64 ≤ c.k then
    let m := memory n c.tables c.blocks c.binaryPoint
    ⟨⟨c,.active s.2 m.value⟩,m.work+3⟩
  else ⟨⟨c,.fallback⟩,2⟩

/-- A uniform startup entry point. The returned configuration is ready for
all subsequent calls to `PolylogExecution.step`. -/
def build (n : ℕ) : Result (Σ c, PolylogExecution.State n c) :=
  let s := scalars n
  let out := boot n s.value
  ⟨out.value,s.work+out.work⟩

theorem build_value (n : ℕ) :
    (build n).value = ⟨PolylogExecution.config n, PolylogExecution.start n (PolylogExecution.config n)⟩ := by
  change (boot n (scalars n).value).value = _
  rw [scalars_value]
  simp only [boot,PolylogExecution.start]
  split <;> simp only [memory_value]

def coefficient := 27*recipe.nodes+1+8*12000

/-- Uniform linear initialization, including rejected stages, exact
calibration, cache interning, the binary-point write and all sparse tables. -/
theorem build_work (n : ℕ) : (build n).work ≤ coefficient*(n+1) := by
  have s := scalars_work n
  have l := logPower_linear n 2
  let A := logCap n
  change (A+1)^2 ≤ 8*(n+1) at l
  let c := PolylogExecution.config n
  have e : (scalars n).value = (c,Controller.horizon n) := scalars_value n
  change (scalars n).work + (boot n (scalars n).value).work ≤ _
  rw [e]
  simp only [boot]
  by_cases hk : 64 ≤ c.k
  · rw [if_pos hk]
    have m := memory_work n c.tables c.blocks c.binaryPoint
    have bb : c.blocks ≤ 5+(A+1)*3 := PolylogSchedule.capacity_bits hk (le_refl _)
    have tt : c.tables = 13+6*(A+1) := rfl
    have b2 := Nat.pow_le_pow_left (Nat.add_le_add_right bb 1) 2
    have mw : (memory n c.tables c.blocks c.binaryPoint).work ≤ 10000*(A+1)^2 := by
      apply m.trans; rw [tt]; nlinarith
    change (scalars n).work ≤ _ + 1000*(A+1)^2 at s
    unfold coefficient; dsimp only; nlinarith
  · rw [if_neg hk]
    change (scalars n).work ≤ _ + 1000*(A+1)^2 at s
    unfold coefficient; dsimp only; nlinarith

end SortingAdversary.Continuous.PolylogStartup
