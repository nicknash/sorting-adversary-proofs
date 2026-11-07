import SortingAdversary.Optimal.MeasuredPin
import SortingAdversary.Optimal.MeasuredOrdinaryTypes
import SortingAdversary.Optimal.MeasuredLocalOracle
import SortingAdversary.Optimal.HubWork
import SortingAdversary.Optimal.CalibrationWork
import SortingAdversary.Optimal.OrdinaryPromotion

/-!
# Measured ordinary calibrated promotions

The interval, current dyadic block, sorted hub, physical promotion and
post-split singleton record are all produced by measured routines. The
original ordinary move occurs only in erased equality certificates.
-/

namespace SortingAdversary.Optimal.MeasuredOrdinaryPromotion

open PrimitiveWork WidthRepair RepresentationWork OrdinaryPromotion SeparatedPins
open HubSelector

variable {n K : ℕ} {s : State n}

/-- Successful extraction from the measured finite selector. The dummy is
never returned, as certified by the already proved selector existence. -/
def selectNonempty (order : Equiv.Perm (Fin (K + 1)))
    (get : Fin (K + 1) → Result (Fin (K + 1)))
    (heq : ∀ i, (get i).value = order i) (lower upper : ℕ)
    (hupper : upper ≤ K + 1) (hroom : lower < upper) :
    Result {block : Block // BatchWindows.selectWindow order lower upper ∅ = some block} := by
  let rank := HubSortWork.paletteRank get
  let selected := HubWork.selectWindow (K + 1) rank lower upper []
  have hrank := HubSortWork.paletteRank_value order get heq
  have hselected : selected.value = BatchWindows.selectWindow order lower upper ∅ := by
    simpa only [selected, List.toFinset_nil] using
      HubWork.selectWindow_value order rank hrank lower upper []
  refine ⟨⟨selected.value.getD ⟨⟨0, 0⟩, 0, 0⟩, ?_⟩, selected.work + 1⟩
  obtain ⟨block, hb⟩ := BatchWindows.selectWindow_exists (lower := lower) (upper := upper) order ∅ hupper (by
    simp only [vetoCost, Finset.sum_empty]
    omega)
  rw [hselected, hb, Option.getD_some]

theorem selectNonempty_value (order : Equiv.Perm (Fin (K + 1)))
    (get : Fin (K + 1) → Result (Fin (K + 1)))
    (heq : ∀ i, (get i).value = order i) (lower upper : ℕ)
    (hupper : upper ≤ K + 1) (hroom : lower < upper) :
    (selectNonempty order get heq lower upper hupper hroom).value =
      OrdinaryPromotion.selectNonempty order lower upper hupper hroom := by
  apply Subtype.ext
  exact Option.some.inj ((selectNonempty order get heq lower upper hupper hroom).value.property.symm.trans
    (OrdinaryPromotion.selectNonempty order lower upper hupper hroom).property)

theorem selectNonempty_work_le (order : Equiv.Perm (Fin (K + 1)))
    (get : Fin (K + 1) → Result (Fin (K + 1)))
    (heq : ∀ i, (get i).value = order i) (lower upper : ℕ)
    (hupper : upper ≤ K + 1) (hroom : lower < upper) (A : ℕ)
    (hA : ∀ i, (get i).work ≤ A) :
    (selectNonempty order get heq lower upper hupper hroom).work ≤
      HubWork.windowPolynomial (K + 1) (A + 1) 0 + 1 := by
  exact Nat.add_le_add_right
    (HubWork.selectWindow_polynomial (K + 1) (HubSortWork.paletteRank get) lower upper [] (A + 1)
      (HubSortWork.paletteRank_work_le get A hA)) 1

theorem choice_ext {v : Fin n} (first second : Choice s v)
    (hl : first.lower = second.lower) (hu : first.upper = second.upper)
    (hb : first.block = second.block) (hc : first.colour = second.colour) : first = second := by
  cases first
  cases second
  dsimp only at hl hu hb hc
  cases hl
  cases hu
  cases hb
  cases hc
  rfl

structure Chosen {v : Fin n} (expected : Choice s v) where
  choice : Choice s v
  exact : choice = expected

/-- Two measured CDF scans, a measured block search, and a measured batch
sort construct every data field of the calibrated choice. -/
def choose (a : LocalAccess s) (H d : ℕ) (g : LocalOracle.SparseBounds s.rows H d)
    (R : ℚ) (hR : 0 ≤ R) (v : Fin n)
    (hmark : IsolatedAccuracy.MarkCondition s.rows.view H d R (1 / 16) v)
    (cdf : ℕ → Result ℚ)
    (heq : ∀ cut, (cdf cut).value = LocalOracle.qCDF s.rows H d R (1 / 16) v cut) :
    Result (Chosen (OrdinaryPromotion.choose s H d g R hR v hmark)) := by
  let interval := CalibrationWork.interval (s := s) cdf
  have hi : interval.value =
      ((OrdinaryPromotion.choose s H d g R hR v hmark).lower,
       (OrdinaryPromotion.choose s H d g R hR v hmark).upper) :=
    CalibrationWork.interval_value s H d g R hR v hmark cdf heq
  have hl := congrArg Prod.fst hi
  have hu := congrArg Prod.snd hi
  have ordered : interval.value.1 ≤ interval.value.2 := by
    rw [hl, hu]
    exact (OrdinaryPromotion.choose s H d g R hR v hmark).ordered
  let window := OrdinaryPromotion.inputWindow interval.value.1 interval.value.2
  have hw := OrdinaryPromotion.inputWindow_bounds interval.value.1 interval.value.2 ordered
  let selected := selectNonempty s.order a.order a.order_value window.1 window.2 hw.2.2.2 hw.2.1
  have hb : selected.value.val = (OrdinaryPromotion.choose s H d g R hR v hmark).block := by
    apply Option.some.inj
    calc
      some selected.value.val = BatchWindows.selectWindow s.order window.1 window.2 ∅ :=
        selected.value.property.symm
      _ = some (OrdinaryPromotion.choose s H d g R hR v hmark).block := by
        dsimp only [window]
        rw [hl, hu]
        exact (OrdinaryPromotion.choose s H d g R hR v hmark).selected
  let rank := HubSortWork.paletteRank a.order
  have hrank : HubSortWork.rankValues rank = BatchWindows.paletteRank s.order :=
    HubSortWork.paletteRank_value s.order a.order a.order_value
  have hinj : Function.Injective (HubSortWork.rankValues rank) := by
    rw [hrank]
    exact BatchWindows.paletteRank_injective _
  let hub := HubSortWork.hubColour rank selected.value.val
  have hh : hub.value = HubSelector.hubColour (BatchWindows.paletteRank s.order)
      (BatchWindows.paletteRank_injective s.order) (OrdinaryPromotion.choose s H d g R hR v hmark).block := by
    dsimp only [hub]
    rw [HubSortWork.hubColour_value rank hinj]
    simp only [hrank, hb]
  let position := rank hub.value
  have hp : position.value = (OrdinaryPromotion.choose s H d g R hR v hmark).colour.val := by
    change HubSortWork.rankValues rank hub.value = _
    rw [hrank, hh]
    exact (OrdinaryPromotion.choose s H d g R hR v hmark).rank_eq.symm
  let colour : Fin (s.pool.palette + 1) := ⟨position.value, by
    rw [hp]
    exact (OrdinaryPromotion.choose s H d g R hR v hmark).colour.isLt⟩
  have hc : colour = (OrdinaryPromotion.choose s H d g R hR v hmark).colour := Fin.ext hp
  let choice : Choice s v :=
    { lower := interval.value.1
      upper := interval.value.2
      ordered := ordered
      block := selected.value.val
      selected := selected.value.property
      colour := colour
      rank_eq := by rw [hc, hb]; exact (OrdinaryPromotion.choose s H d g R hR v hmark).rank_eq
      in_interval := by rw [hl, hu, hc]; exact (OrdinaryPromotion.choose s H d g R hR v hmark).in_interval
      supported := by rw [hc]; exact (OrdinaryPromotion.choose s H d g R hR v hmark).supported
      count := by rw [hl, hu, hc]; exact (OrdinaryPromotion.choose s H d g R hR v hmark).count
      interior := by rw [hl, hu, hc]; exact (OrdinaryPromotion.choose s H d g R hR v hmark).interior }
  exact ⟨⟨choice, choice_ext _ _ hl hu hb hc⟩,
    interval.work + selected.work + hub.work + position.work + 8⟩

def chooseBound (palette A C : ℕ) : ℕ :=
  (2 * CalibrationWork.firstBound palette (C + 1) + 1) +
    (HubWork.windowPolynomial (palette + 1) (A + 1) 0 + 1) +
    (11 * (palette + 1) + 10 + (palette + 2) ^ 2 * (2 * (A + 1) + 5)) + (A + 1) + 8

theorem choose_work_le (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (H d : ℕ) (g : LocalOracle.SparseBounds s.rows H d)
    (R : ℚ) (hR : 0 ≤ R) (v : Fin n)
    (hmark : IsolatedAccuracy.MarkCondition s.rows.view H d R (1 / 16) v)
    (cdf : ℕ → Result ℚ)
    (heq : ∀ cut, (cdf cut).value = LocalOracle.qCDF s.rows H d R (1 / 16) v cut)
    (C : ℕ) (hC : ∀ cut, (cdf cut).work ≤ C) :
    (choose a H d g R hR v hmark cdf heq).work ≤ chooseBound s.pool.palette A C := by
  let interval := CalibrationWork.interval (s := s) cdf
  have hi : interval.value =
      ((OrdinaryPromotion.choose s H d g R hR v hmark).lower,
       (OrdinaryPromotion.choose s H d g R hR v hmark).upper) :=
    CalibrationWork.interval_value s H d g R hR v hmark cdf heq
  have ordered : interval.value.1 ≤ interval.value.2 := by
    rw [hi]
    exact (OrdinaryPromotion.choose s H d g R hR v hmark).ordered
  let window := OrdinaryPromotion.inputWindow interval.value.1 interval.value.2
  have hw := OrdinaryPromotion.inputWindow_bounds interval.value.1 interval.value.2 ordered
  let selected := selectNonempty s.order a.order a.order_value window.1 window.2 hw.2.2.2 hw.2.1
  let rank := HubSortWork.paletteRank a.order
  have hrank : HubSortWork.rankValues rank = BatchWindows.paletteRank s.order :=
    HubSortWork.paletteRank_value s.order a.order a.order_value
  have hinj : Function.Injective (HubSortWork.rankValues rank) := by
    rw [hrank]
    exact BatchWindows.paletteRank_injective _
  have havailable : selected.value.val ∈ allBlocks (s.pool.palette + 1) :=
    (selected_spec selected.value.property).1
  have hinterval := CalibrationWork.interval_work_le (s := s) cdf C hC
  have hselected := selectNonempty_work_le s.order a.order a.order_value window.1 window.2
    hw.2.2.2 hw.2.1 A hA.order
  have hhub := HubWork.current_hub_work_le (s.pool.palette + 1) rank hinj selected.value.val
    havailable (A + 1) (HubSortWork.paletteRank_work_le a.order A hA.order)
  have hposition := HubSortWork.paletteRank_work_le a.order A hA.order
    (HubSortWork.hubColour rank selected.value.val).value
  change interval.work + selected.work + (HubSortWork.hubColour rank selected.value.val).work +
    (rank (HubSortWork.hubColour rank selected.value.val).value).work + 8 ≤ _
  change interval.work ≤ _ at hinterval
  change selected.work ≤ _ at hselected
  change (rank (HubSortWork.hubColour rank selected.value.val).value).work ≤ _ at hposition
  change _ ≤ 11 * (s.pool.palette + 1) + 10 +
    (s.pool.palette + 2) ^ 2 * (2 * (A + 1) + 5) at hhub
  unfold chooseBound
  omega

/-- The charge is constructed as one natural product and its denominator-one
rational embedding; no unmeasured rational multiplication is performed. -/
def toPin (a : LocalAccess s) {v : Fin n} (choice : Choice s v)
    (hv : s.pool.pins v = none) (hm : HasMate s.pool v) :
    Result (MeasuredPin.Output (choice.toPin hv hm)) := by
  let charge : ℚ := (16 * choice.width : ℕ)
  have hcharge : charge = (choice.toPin hv hm).charge := by
    simp only [charge, Choice.toPin, Nat.cast_mul, Nat.cast_ofNat]
  have retained : (s.pool.system.count : ℚ) ≤ charge *
      (Promotion.promote s.pool.system s.pool.pins s.pool.invariant s.pool.pin_bounds
        v hv choice.colour choice.supported).system.count := by
    rw [hcharge]
    exact (choice.toPin hv hm).retained
  let result := MeasuredPin.pin a v hv choice.colour choice.supported hm charge retained
  have hcanonical : MeasuredPin.canonical s v hv choice.colour choice.supported hm charge retained =
      choice.toPin hv hm := MeasuredPin.update_ext _ _ rfl rfl hcharge
  exact ⟨⟨result.value.update, result.value.access, result.value.exact.trans hcanonical,
    result.value.bounded⟩, result.work + 8⟩

theorem toPin_work_le (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    {v : Fin n} (choice : Choice s v) (hv : s.pool.pins v = none) (hm : HasMate s.pool v) :
    (toPin a choice hv hm).work ≤ MeasuredPin.workBound n s.pool.palette A + 8 := by
  apply Nat.add_le_add_right
  exact MeasuredPin.pin_work_le a hA _ _ _ _ _ _ _

theorem hubRecord_ext {update : PinUpdate s} (first second : HubRecord update)
    (hb : first.births = second.births) (ho : HEq first.order second.order)
    (hblock : first.block = second.block) : first = second := by
  cases first
  cases second
  dsimp only at hb ho hblock
  cases hb
  have heq := eq_of_heq ho
  cases heq
  cases hblock
  rfl

structure Recorded {v : Fin n} (choice : Choice s v)
    (hv : s.pool.pins v = none) (hm : HasMate s.pool v) (update : PinUpdate s) where
  record : HubRecord update
  exact : HEq record (choice.record hv hm)

/-- Wide choices preserve their computed historical block. Short choices run
an actual measured singleton selection using the cached post-pin palette. -/
def record {v : Fin n} (choice : Choice s v) (hv : s.pool.pins v = none)
    (hm : HasMate s.pool v) (update : PinUpdate s) (hu : update = choice.toPin hv hm)
    (a : LocalAccess update.next) : Result (Recorded choice hv hm update) :=
  if hlarge : 8 ≤ choice.width then
    let result : HubRecord update :=
      { births := s.pool.palette + 1
        order := s.order
        block := choice.block
        available := choice.available
        destination := by
          rw [hu]
          exact choice.identity.symm.trans (choice.interior_destination hv hm hlarge).symm
        born := Nat.succ_le_succ update.result.palette_bounds.1
        orderPreserved := OrdinaryPromotion.promotion_rank_preserved update
        tariff := by
          intro M hM
          rw [hu]
          change (16 : ℚ) * (choice.width : ℚ) ≤ _
          exact_mod_cast choice.wide_tariff hlarge M hM }
    ⟨⟨result, by
      cases hu
      apply heq_of_eq
      simp only [Choice.record, dif_pos hlarge]
      rfl⟩, 8⟩
  else
    let selected := selectNonempty update.data.order a.order a.order_value
      update.result.destination.val (update.result.destination.val + 1)
      update.result.destination.isLt (Nat.lt_succ_self _)
    have hb : selected.value.val =
        (OrdinaryPromotion.singletonBlock update.data.order update.result.destination).val :=
      congrArg Subtype.val (selectNonempty_value update.data.order a.order a.order_value _ _ _ _)
    let result : HubRecord update :=
      { births := update.result.palette + 1
        order := update.data.order
        block := selected.value.val
        available := (selected_spec selected.value.property).1
        destination := by
          rw [hb]
          exact OrdinaryPromotion.singletonBlock_identity _ _
        born := le_rfl
        orderPreserved := fun _ _ _ _ => Iff.rfl
        tariff := by
          intro M _
          have hs : selected.value.val.size = 1 := by
            rw [hb]
            exact OrdinaryPromotion.singletonBlock_size _ _
          have h : 16 * choice.width ≤ 128 * selected.value.val.size *
              (M - selected.value.val.level + 2) := by
            rw [hs]
            omega
          have hc : update.charge = (16 : ℚ) * (choice.width : ℚ) := congrArg PinUpdate.charge hu
          rw [hc]
          exact_mod_cast h }
    ⟨⟨result, by
      cases hu
      apply heq_of_eq
      simp only [Choice.record, dif_neg hlarge]
      exact hubRecord_ext result _ rfl HEq.rfl hb⟩, selected.work + 8⟩

set_option maxHeartbeats 2000000 in
theorem record_work_le {v : Fin n} (choice : Choice s v) (hv : s.pool.pins v = none)
    (hm : HasMate s.pool v) (update : PinUpdate s) (hu : update = choice.toPin hv hm)
    (a : LocalAccess update.next) {A : ℕ} (hA : AccessBound a A) :
    (record choice hv hm update hu a).work ≤
      HubWork.windowPolynomial (update.result.palette + 1) (A + 1) 0 + 9 := by
  unfold record
  split
  · dsimp only
    omega
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using
      Nat.add_le_add_right (selectNonempty_work_le update.data.order a.order a.order_value
        _ _ _ _ A hA.order) 8

theorem move_eq {v : Fin n} (choice : Choice s v) (hv : s.pool.pins v = none)
    (hm : HasMate s.pool v) (update : PinUpdate s) (hu : update = choice.toPin hv hm)
    (record : HubRecord update) (hr : HEq record (choice.record hv hm)) :
    (⟨update, record⟩ : Move s) = ⟨choice.toPin hv hm, choice.record hv hm⟩ := by
  cases hu
  have heq := eq_of_heq hr
  cases heq
  rfl

attribute [local irreducible] choose toPin record

set_option maxHeartbeats 2000000 in
/-- A complete ordinary move whose data is produced by the measured interval,
hub, pin, and record computations above. -/
def make (a : LocalAccess s) (H d : ℕ) (g : LocalOracle.SparseBounds s.rows H d)
    (R : ℚ) (hR : 0 ≤ R) (v : Fin n)
    (hmark : IsolatedAccuracy.MarkCondition s.rows.view H d R (1 / 16) v)
    (hv : s.pool.pins v = none) (hm : HasMate s.pool v)
    (cdf : ℕ → Result ℚ)
    (heq : ∀ cut, (cdf cut).value = LocalOracle.qCDF s.rows H d R (1 / 16) v cut) :
    Result (Output s H d g R hR v hmark hv hm) := by
  let chosen := choose a H d g R hR v hmark cdf heq
  let physical := toPin a chosen.value.choice hv hm
  let historical := record chosen.value.choice hv hm physical.value.update
    physical.value.exact physical.value.access
  let result : Move s := ⟨physical.value.update, historical.value.record⟩
  have hfirst : result = ⟨chosen.value.choice.toPin hv hm, chosen.value.choice.record hv hm⟩ :=
    move_eq chosen.value.choice hv hm physical.value.update physical.value.exact
      historical.value.record historical.value.exact
  have hfinal : (⟨chosen.value.choice.toPin hv hm, chosen.value.choice.record hv hm⟩ : Move s) =
      OrdinaryPromotion.make s H d g R hR v hmark hv hm := by
    rw [chosen.value.exact]
    rfl
  exact ⟨⟨result, physical.value.access, hfirst.trans hfinal, physical.value.bounded⟩,
    chosen.work + physical.work + historical.work + 4⟩

def workBound (n palette A C : ℕ) : ℕ :=
  chooseBound palette A C + (MeasuredPin.workBound n palette A + 8) +
    (HubWork.windowPolynomial (palette + 2) 3 0 + 9) + 4

set_option maxHeartbeats 2000000 in
theorem make_work_le (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (H d : ℕ) (g : LocalOracle.SparseBounds s.rows H d)
    (R : ℚ) (hR : 0 ≤ R) (v : Fin n)
    (hmark : IsolatedAccuracy.MarkCondition s.rows.view H d R (1 / 16) v)
    (hv : s.pool.pins v = none) (hm : HasMate s.pool v)
    (cdf : ℕ → Result ℚ)
    (heq : ∀ cut, (cdf cut).value = LocalOracle.qCDF s.rows H d R (1 / 16) v cut)
    (C : ℕ) (hC : ∀ cut, (cdf cut).work ≤ C) :
    (make a H d g R hR v hmark hv hm cdf heq).work ≤ workBound n s.pool.palette A C := by
  let chosen := choose a H d g R hR v hmark cdf heq
  let physical := toPin a chosen.value.choice hv hm
  let historical := record chosen.value.choice hv hm physical.value.update
    physical.value.exact physical.value.access
  have hchoose := choose_work_le a hA H d g R hR v hmark cdf heq C hC
  have hpin := toPin_work_le a hA chosen.value.choice hv hm
  have hrecord := record_work_le chosen.value.choice hv hm physical.value.update
    physical.value.exact physical.value.access physical.value.bounded
  have hpalette := physical.value.update.result.palette_bounds.2
  have hmono : HubWork.windowPolynomial (physical.value.update.result.palette + 1) 3 0 ≤
      HubWork.windowPolynomial (s.pool.palette + 2) 3 0 := by
    unfold HubWork.windowPolynomial
    apply Nat.mul_le_mul_right
    apply Nat.pow_le_pow_left
    omega
  change historical.work ≤
    HubWork.windowPolynomial (physical.value.update.result.palette + 1) 3 0 + 9 at hrecord
  change chosen.work ≤ _ at hchoose
  change physical.work ≤ _ at hpin
  change chosen.work + physical.work + historical.work + 4 ≤ _
  unfold workBound
  omega

/-- Instantiate the CDF callback with the actual counted local DP. The
radius is an already computed stage datum with an erased exactness proof. -/
def atRadius (a : LocalAccess s) (H d : ℕ) (g : LocalOracle.SparseBounds s.rows H d)
    (R : ℚ) (hR : 0 ≤ R) (v : Fin n)
    (hmark : IsolatedAccuracy.MarkCondition s.rows.view H d R (1 / 16) v)
    (hv : s.pool.pins v = none) (hm : HasMate s.pool v)
    (radius : ℕ)
    (hr : radius = H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R (1 / 16)) :
    Result (Output s H d g R hR v hmark hv hm) :=
  let answer := make a H d g R hR v hmark hv hm (MeasuredLocalOracle.cdf a radius v) (by
    intro cut
    rw [hr]
    exact MeasuredLocalOracle.cdf_value a H d R (1 / 16) v cut)
  ⟨answer.value, answer.work + 1⟩

theorem atRadius_work_le (a : LocalAccess s) {A : ℕ} (hA : AccessBound a A)
    (H d : ℕ) (g : LocalOracle.SparseBounds s.rows H d)
    (R : ℚ) (hR : 0 ≤ R) (v : Fin n)
    (hmark : IsolatedAccuracy.MarkCondition s.rows.view H d R (1 / 16) v)
    (hv : s.pool.pins v = none) (hm : HasMate s.pool v)
    (radius : ℕ)
    (hr : radius = H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R (1 / 16))
    (c : ℕ) (hn : n ≠ 0)
    (hb : (GraphBalls.ball s.rows.active v radius).card ≤ Nat.log 2 n)
    (hK : s.pool.palette + 1 ≤ c * n) :
    (atRadius a H d g R hR v hmark hv hm radius hr).work ≤
      workBound n s.pool.palette A (MeasuredLocalOracle.cdfBound n c A) + 1 := by
  apply Nat.add_le_add_right
  exact make_work_le a hA H d g R hR v hmark hv hm _ _
    (MeasuredLocalOracle.cdfBound n c A)
    (fun cut => MeasuredLocalOracle.cdf_work a A hA radius v cut c hn hb hK)

/-- A concrete ordinary executor for the fixed accepted-stage parameters.
The stage initialization pays for `radius`; every local query and update is
paid by `atRadius`. -/
def executor (H d : ℕ) (R : ℚ) (radius : ℕ)
    (hr : radius = H * LocalParameters.sweepCount H (LocalAccuracy.influenceSize H d) R (1 / 16)) :
    Executor n H d R :=
  fun access _ g hR v hmark hv hm => atRadius access H d g R hR v hmark hv hm radius hr

end SortingAdversary.Optimal.MeasuredOrdinaryPromotion
