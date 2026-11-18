import SortingAdversary.Continuous.DensityCertificates
import SortingAdversary.Continuous.Precision

/-!
# The fallback anchor computed from a binary prefix

The walls lie on a common grid of `F` bits. A binary search queries
`l + 2⁻ˢ ≤ r` to find the scale of their separation. Truncate the lower
wall at bit `s + 2` and add three units there. The resulting rational lies
in the middle half and pays both density tariffs at its reduced dyadic level.

The search counts comparisons of exact dyadic numbers. Its rational
specification below does not assign unit word-RAM cost to these comparisons.
-/

namespace SortingAdversary.Continuous.PolylogAnchor

open FiniteAveraging Certificates OrderRegion Density MeasureTheory

/-- The second component counts predicate evaluations. Under the bracket
invariant, the first component is the first index satisfying the predicate. -/
def bisect (test : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, hi => (hi, 0)
  | rounds + 1, lo, hi =>
    let mid := (lo + hi) / 2
    let result := if test mid then bisect test rounds lo mid
      else bisect test rounds (mid + 1) hi
    (result.1, result.2 + 1)

@[simp] theorem bisect_tests (test : ℕ → Bool) (rounds lo hi : ℕ) :
    (bisect test rounds lo hi).2 = rounds := by
  induction rounds generalizing lo hi with
  | zero => rfl
  | succ j ih =>
    simp only [bisect]
    split <;> simp [ih]

theorem bisect_spec (test : ℕ → Bool)
    (mono : ∀ i j, i ≤ j → test i = true → test j = true)
    (rounds lo hi : ℕ) (hle : lo ≤ hi) (hspan : hi - lo < 2 ^ rounds)
    (hlo : ∀ i, i < lo → test i = false) (hhi : test hi = true) :
    let s := (bisect test rounds lo hi).1
    s ≤ hi ∧ test s = true ∧ ∀ i, i < s → test i = false := by
  induction rounds generalizing lo hi with
  | zero =>
    simp only [pow_zero] at hspan
    obtain rfl : lo = hi := by omega
    exact ⟨le_rfl, hhi, hlo⟩
  | succ j ih =>
    rw [pow_succ] at hspan
    let mid := (lo + hi) / 2
    have hmid : lo ≤ mid ∧ mid ≤ hi := by dsimp [mid]; omega
    by_cases htest : test mid = true
    · have hrec := ih lo mid hmid.1 (by dsimp [mid]; omega) hlo htest
      simpa only [bisect, ← show mid = (lo + hi) / 2 from rfl, htest, if_true] using
        And.intro (hrec.1.trans hmid.2) hrec.2
    · have hmlt : mid < hi := by
        apply Nat.lt_of_le_of_ne hmid.2
        intro he
        exact htest (he ▸ hhi)
      have hrec := ih (mid + 1) hi (by omega) (by dsimp [mid]; omega) (by
        intro i hi'
        cases h : test i with
        | false => rfl
        | true => exact (htest (mono i mid (by omega) h)).elim) hhi
      simpa only [bisect, ← show mid = (lo + hi) / 2 from rfl, Bool.eq_false_iff.mpr htest, Bool.false_eq_true, if_false] using hrec

/-- One unit at fractional bit `s`. -/
def unit (s : ℕ) : ℚ := 1 / (2 : ℚ) ^ s

private theorem unit_pos (s : ℕ) : 0 < unit s := by unfold unit; positivity

private theorem unit_antitone {i j : ℕ} (h : i ≤ j) : unit j ≤ unit i :=
  one_div_le_one_div_of_le (by positivity : (0 : ℚ) < 2 ^ i)
    (pow_le_pow_right₀ (by norm_num) h)

private theorem twice_unit_succ (s : ℕ) : 2 * unit (s + 1) = unit s := by
  rw [unit, unit, pow_succ]
  field_simp

/-- An executable specification of the bit index found by the width search.
The predicate only adds a single bit to a stored wall and compares with the other wall. -/
def widthSearch (F : ℕ) (l r : ℚ) : ℕ × ℕ :=
  bisect (fun s => decide (l + unit s ≤ r)) (Nat.log 2 F + 1) 0 F

@[simp] theorem widthSearch_tests (F : ℕ) (l r : ℚ) :
    (widthSearch F l r).2 = Nat.log 2 F + 1 := bisect_tests _ _ _ _

/-- The returned bit is no deeper than the stored walls. Its unit is the
largest power of two no greater than the width, including width one. -/
theorem widthSearch_of_bound {F : ℕ} {l r : ℚ} (hw : unit F ≤ r - l) (hW : r - l ≤ 1) :
    let s := (widthSearch F l r).1
    s ≤ F ∧ unit s ≤ r - l ∧ r - l < 2 * unit s := by
  let test := fun s => decide (l + unit s ≤ r)
  have mono : ∀ i j, i ≤ j → test i = true → test j = true := by
    intro i j hij ht
    exact decide_eq_true (by linarith [of_decide_eq_true ht, unit_antitone hij])
  have h := bisect_spec test mono (Nat.log 2 F + 1) 0 F (Nat.zero_le _)
    (by simpa using Nat.lt_pow_succ_log_self (by decide : 1 < 2) F)
    (by intro i hi; omega) (decide_eq_true (by linarith))
  let s := (widthSearch F l r).1
  change s ≤ F ∧ unit s ≤ r - l ∧ r - l < 2 * unit s
  have hs : test s = true := h.2.1
  refine ⟨h.1, by linarith [of_decide_eq_true hs], ?_⟩
  cases he : s with
  | zero => simp [unit]; linarith
  | succ j =>
    have hprev : test j = false := h.2.2 j (show j < s by omega)
    have hj : ¬ l + unit j ≤ r := of_decide_eq_false hprev
    linarith [twice_unit_succ j]

theorem widthSearch_spec {F : ℕ} {l r : ℚ} (hl : OnDyadicGrid F l) (hr : OnDyadicGrid F r)
    (hlr : l < r) (hW : r - l ≤ 1) :
    let s := (widthSearch F l r).1
    s ≤ F ∧ unit s ≤ r - l ∧ r - l < 2 * unit s :=
  widthSearch_of_bound (Precision.interval_width_ge hl hr hlr) hW

/-- Formula (2) of the note, expressed in terms of the bit index. -/
def atScale (s : ℕ) (l : ℚ) : ℚ :=
  let h := unit (s + 2)
  ((⌊l / h⌋ : ℤ) + 3 : ℚ) * h

def fallback (F : ℕ) (l r : ℚ) : ℚ := atScale (widthSearch F l r).1 l

theorem atScale_onGrid (s : ℕ) (l : ℚ) : OnDyadicGrid (s + 2) (atScale s l) := by
  refine ⟨⌊l / unit (s + 2)⌋ + 3, ?_⟩
  simp [atScale, unit, div_eq_mul_inv]

/-- Truncation moves the lower wall by less than one unit. Adding three
units therefore places the anchor in the advertised middle half. -/
theorem atScale_middle {s : ℕ} {l r : ℚ} (hlo : unit s ≤ r - l)
    (hhi : r - l < 2 * unit s) :
    l + (r - l) / 4 ≤ atScale s l ∧ atScale s l ≤ r - (r - l) / 4 := by
  let h := unit (s + 2)
  have hp : 0 < h := unit_pos _
  have hunit : 4 * h = unit s := by
    dsimp [h]
    linarith [twice_unit_succ s, twice_unit_succ (s + 1)]
  have ha := (le_div_iff₀ hp).mp (Int.floor_le (l / h))
  have hb := (div_lt_iff₀ hp).mp (Int.lt_floor_add_one (l / h))
  change l + (r - l) / 4 ≤ ((⌊l / h⌋ : ℤ) + 3 : ℚ) * h ∧
    ((⌊l / h⌋ : ℤ) + 3 : ℚ) * h ≤ r - (r - l) / 4
  constructor <;> linarith

theorem fallback_onGrid {F : ℕ} {l r : ℚ} (hl : OnDyadicGrid F l) (hr : OnDyadicGrid F r)
    (hlr : l < r) (hW : r - l ≤ 1) : OnDyadicGrid (F + 2) (fallback F l r) :=
  Precision.grid_mono (atScale_onGrid _ _) (Nat.add_le_add_right (widthSearch_spec hl hr hlr hW).1 2)

/-- Enlarging the grid capacity changes the search budget but not the anchor. -/
theorem fallback_cap_independent {F G : ℕ} {l r : ℚ}
    (hcapF : unit F ≤ r - l) (hcapG : unit G ≤ r - l) (hW : r - l ≤ 1) : fallback F l r = fallback G l r := by
  have hF := widthSearch_of_bound hcapF hW
  have hG := widthSearch_of_bound hcapG hW
  suffices he : (widthSearch F l r).1 = (widthSearch G l r).1 by simp [fallback, he]
  have unique {i j : ℕ} (hi : unit i ≤ r - l) (hj : r - l < 2 * unit j) : j ≤ i := by
    by_contra! hn
    have hu := unit_antitone (show i + 1 ≤ j by omega)
    linarith [twice_unit_succ i]
  exact le_antisymm (unique hG.2.1 hF.2.2) (unique hF.2.1 hG.2.2)

/-- Refine the given label, then propagate the resulting walls. The two-bit
bound applies to the full stored system after both operations. -/
theorem fallback_refine_grid {n F : ℕ} (s : TreeState.State n ℚ) (x : Fin n)
    (order : List (Fin n)) (hD : Precision.BoundsOnGrid s.system F)
    (hw : s.system.lower x < s.system.upper x)
    (hW : s.system.upper x - s.system.lower x ≤ 1) :
    Precision.BoundsOnGrid (TreeState.normalize (TreeState.refineAt s x
      (fallback F (s.system.lower x) (s.system.upper x))) order).system (F + 2) :=
  Precision.normalize_onGrid _ _ order (Precision.resetCoordinate_onGrid _ _ _ _
    (Precision.bounds_mono hD (by omega)) (fallback_onGrid (hD.1 x) (hD.2 x) hw hW))

/-- After `t` anchor writes, each either on the fixed central-test grid or
at most two bits deeper than the preceding walls, precision is at most
`A + 2t`. This permits arbitrary interleaving of the two kinds of writes. -/
theorem precision_after_writes (A : ℕ) (bits : ℕ → ℕ) (hzero : bits 0 ≤ A)
    (hstep : ∀ t, bits (t + 1) ≤ max A (bits t + 2)) (t : ℕ) :
    bits t ≤ A + 2 * t := by
  induction t with
  | zero => simpa using hzero
  | succ t ih => exact (hstep t).trans (max_le (by omega) (by omega))

/-- The certificate uses the reduced level of the *returned* coordinate. -/
theorem fallback_anchor {F : ℕ} {l r : ℚ} (hcap : unit F ≤ r - l)
    (hlr : l < r) (hl0 : 0 ≤ l) (hr1 : r ≤ 1) :
    ∃ c : DyadicAnchor, c.coordinate = fallback F l r ∧
      (l + (r - l) / 4 ≤ c.coordinate ∧ c.coordinate ≤ r - (r - l) / 4) ∧
      (r - l) / 4 < unit c.1 := by
  let s := (widthSearch F l r).1
  have hs := widthSearch_of_bound hcap (by linarith)
  have hm := atScale_middle hs.2.1 hs.2.2
  obtain ⟨c, hc, he⟩ := exists_dyadicAnchor_of_grid (atScale_onGrid s l)
    (show 0 < atScale s l by linarith [hm.1]) (show atScale s l < 1 by linarith [hm.2])
  refine ⟨c, hc, hc ▸ hm, ?_⟩
  have he' : c.1 ≤ s + 1 := by omega
  have hu := unit_antitone he'
  have hw : r - l < 2 * unit s := hs.2.2
  linarith [twice_unit_succ s]

/-- The extra bit in the prefix rule still leaves enough slack in the
level-minus-four accounting of the original controller. -/
private theorem prefix_density_tariffs {W f : ℝ} {k B m : ℕ}
    (hk : 64 ≤ k) (hB : 1 ≤ B) (hW : 0 < W)
    (hsmall : W < 1 / (2 : ℝ) ^ (2 * k * B))
    (hf : (1 / 4 : ℝ) ^ B / W ≤ f) (hlen : W / 4 < 1 / (2 : ℝ) ^ m) :
    (k : ℝ) < log2 f ∧ stopMass k * m - 4 < log2 f := by
  let L := log2 (1 / W)
  have hL : 2 * (k : ℝ) * B < L := small_width_log hW hsmall
  have hg : L - 2 * B ≤ log2 f := middle_density_log_lower hW hf
  have hm : (m : ℝ) < L + 2 := by
    have h := middle_rounding_level (W := W / 2) (m := m) (by positivity) (by linarith)
    have he : 1 / (W / 2) = (1 / W) * 2 := by ring
    rw [he, log2_mul (by positivity) (by norm_num), log2_two] at h
    dsimp [L]
    linarith
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hk0 : (0 : ℝ) < k := by linarith
  have hs := stopMass_pos (show (1 : ℝ) < k by linarith)
  have hs1 : stopMass k < 1 := by
    unfold stopMass
    have : (0 : ℝ) < 1 / k := by positivity
    linarith
  have heq : (k : ℝ) * stopMass k = k - 1 := by unfold stopMass; field_simp
  have heqL := congrArg (fun z : ℝ => z * L) heq
  have hgain : (k : ℝ) < L - 2 * B := by nlinarith
  have hdiscount : stopMass k * L < L - 2 * B := by
    apply (mul_lt_mul_iff_right₀ hk0).mp
    nlinarith [heqL]
  have hround := mul_lt_mul_of_pos_left hm hs
  exact ⟨hgain.trans_le hg, lt_of_lt_of_le (by nlinarith : stopMass k * m - 4 < L - 2 * B) hg⟩

/-- A failed mass test on a sufficiently narrow canonical interval. Both
gains concern the actual feasible-region density of the chosen label. -/
theorem fallback_tariffs {n : ℕ} (D : System (Fin n) ℚ) (x : Fin n) (F k B : ℕ)
    (hk : 64 ≤ k) (hBpos : 1 ≤ B) (hD : Normalized D.toReal)
    (hB : ComparableDensity.comparableCount D.toReal x ≤ B)
    (hV : 0 < volume (region D.toReal)) (hw : D.lower x < D.upper x)
    (hb : 0 ≤ D.lower x ∧ D.upper x ≤ 1)
    (hcap : unit F ≤ D.upper x - D.lower x)
    (hsmall : D.upper x - D.lower x < 1 / (2 : ℚ) ^ (2 * k * B)) :
    ∃ c : DyadicAnchor, c.coordinate = fallback F (D.lower x) (D.upper x) ∧
      (k : ℝ) < log2 (density D.toReal x (c.coordinate : ℝ)) ∧
      stopMass k * c.1 - 4 < log2 (density D.toReal x (c.coordinate : ℝ)) := by
  obtain ⟨c, hc, hm, hlen⟩ := fallback_anchor hcap hw hb.1 hb.2
  refine ⟨c, hc, ?_⟩
  apply prefix_density_tariffs (W := (D.upper x : ℝ) - D.lower x) hk hBpos
  · exact_mod_cast sub_pos.mpr hw
  · simpa using (Rat.cast_lt (K := ℝ)).mpr hsmall
  · apply ComparableDensity.middle_density_lower D.toReal hD x
      (by exact (Rat.cast_lt (K := ℝ)).mpr hw) (nodeVolume_pos D.toReal hV) B hB
    change ((D.lower x : ℝ) + ((D.upper x : ℝ) - D.lower x) / 4 ≤ (c.coordinate : ℝ)) ∧
      (c.coordinate : ℝ) ≤ (D.upper x : ℝ) - ((D.upper x : ℝ) - D.lower x) / 4
    exact ⟨by exact_mod_cast hm.1, by exact_mod_cast hm.2⟩
  · unfold unit at hlen
    simpa using (Rat.cast_lt (K := ℝ)).mpr hlen

/-- A reference choice of search capacity, valid even on arbitrary rational
inputs. The machine uses its stored grid capacity in its place. -/
def referenceBits (l r : ℚ) : ℕ := (r - l).den.size

theorem referenceBits_spec {l r : ℚ} (hlr : l < r) : unit (referenceBits l r) ≤ r - l := by
  let W := r - l
  have hp : 0 < W := sub_pos.mpr hlr
  have hn : (1 : ℚ) ≤ (W.num : ℚ) := by
    have hp' := Rat.num_pos.mpr hp
    exact_mod_cast (show (1 : ℤ) ≤ W.num by omega)
  have hd : (0 : ℚ) < W.den := by exact_mod_cast W.den_pos
  have hb : (W.den : ℚ) ≤ (2 : ℚ) ^ W.den.size := by
    exact_mod_cast (Nat.lt_size_self W.den).le
  exact (one_div_le_one_div_of_le hd hb).trans
    ((div_le_div_of_nonneg_right hn hd.le).trans_eq (Rat.num_div_den W))

/-- Reference and bounded-capacity prefix choices coincide at every legal
dyadic machine state. -/
theorem fallback_eq_reference {F : ℕ} {l r : ℚ} (hcap : unit F ≤ r - l)
    (hlr : l < r) (hW : r - l ≤ 1) :
    fallback F l r = fallback (referenceBits l r) l r :=
  fallback_cap_independent hcap (referenceBits_spec hlr) hW

end SortingAdversary.Continuous.PolylogAnchor
