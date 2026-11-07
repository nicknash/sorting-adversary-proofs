import SortingAdversary.Optimal.Accounting

/-!
# The entropy budget for groups of promotions

A finite nonnegative array records how many labels in each selected group go
to each child. This file proves directly, without probability spaces, that
conditioning on the group cannot increase destination entropy. If a group of
`h` labels sends at most `r` labels to any one child, its conditional entropy
is at least `h * log (h / r)`.

Consequently disjoint `H`-paths with distinct destinations consume at least
`log H` per selected label, and scale groups with destination multiplicity at
most two consume at least `log (J / 2)` per selected label. Disjointness and
the actual destination multiplicities remain controller obligations; they are
represented here by the finite array and its explicit bounds.

All logarithms are natural logarithms. Zero cells are allowed and contribute
zero through the convention `0 * Real.log x = 0`.
-/

namespace SortingAdversary.Optimal.GroupEntropy

open scoped BigOperators

/-- The weighted log-sum inequality with zero weights allowed. Each `mass i`
is a nonnegative reservoir containing `weight i`; its sum is the total mass
available to this calculation. -/
theorem log_sum_le_mass_ratio {ι : Type*} (s : Finset ι)
    (weight mass : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hcontained : ∀ i ∈ s, weight i ≤ mass i) :
    (∑ i ∈ s, weight i * Real.log (mass i / weight i)) ≤
      (∑ i ∈ s, weight i) *
        Real.log ((∑ i ∈ s, mass i) / (∑ i ∈ s, weight i)) := by
  classical
  let positive := s.filter fun i => 0 < weight i
  have hpositive_subset : positive ⊆ s := Finset.filter_subset _ _
  have hpos (i : ι) (hi : i ∈ positive) : 0 < weight i :=
    (Finset.mem_filter.mp hi).2
  have hmasspos (i : ι) (hi : i ∈ positive) : 0 < mass i :=
    lt_of_lt_of_le (hpos i hi) (hcontained i (hpositive_subset hi))
  have hrestrict (f : ι → ℝ) :
      (∑ i ∈ positive, weight i * f i) = ∑ i ∈ s, weight i * f i := by
    dsimp only [positive]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : 0 < weight i
    · simp [hp]
    · have hz : weight i = 0 := le_antisymm (le_of_not_gt hp) (hweight i hi)
      simp [hz]
  have hweight_sum : (∑ i ∈ positive, weight i) = ∑ i ∈ s, weight i := by
    simpa using hrestrict (fun _ => 1)
  rw [← hrestrict (fun i => Real.log (mass i / weight i)), ← hweight_sum]
  by_cases hnonempty : positive.Nonempty
  · have hW : 0 < ∑ i ∈ positive, weight i := Finset.sum_pos hpos hnonempty
    have hM : 0 < ∑ i ∈ positive, mass i := Finset.sum_pos hmasspos hnonempty
    have hweighted := Accounting.weighted_log_le positive weight
      (fun i => mass i / weight i) hpos (fun i hi => div_pos (hmasspos i hi) (hpos i hi))
    have hcancel :
        (∑ i ∈ positive, weight i * (mass i / weight i)) =
          ∑ i ∈ positive, mass i := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [(hpos i hi).ne']
    rw [hcancel] at hweighted
    have hmasssum : (∑ i ∈ positive, mass i) ≤ ∑ i ∈ s, mass i :=
      Finset.sum_le_sum_of_subset_of_nonneg hpositive_subset
        (fun i hi _ => le_trans (hweight i hi) (hcontained i hi))
    have hratio : (∑ i ∈ positive, mass i) / (∑ i ∈ positive, weight i) ≤
        (∑ i ∈ s, mass i) / (∑ i ∈ positive, weight i) :=
      div_le_div_of_nonneg_right hmasssum hW.le
    have hlog := Real.log_le_log (div_pos hM hW) hratio
    exact hweighted.trans (mul_le_mul_of_nonneg_left hlog hW.le)
  · have hempty : positive = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp [hempty]

section Array

variable {Group Child : Type*} [Fintype Group] [Fintype Child]

/-- The number of labels in one group. -/
def groupSize (cell : Group → Child → ℝ) (g : Group) : ℝ := ∑ c, cell g c

/-- The number of labels sent to one destination. -/
def childSize (cell : Group → Child → ℝ) (c : Child) : ℝ := ∑ g, cell g c

/-- The total number of labels represented by the array. -/
def totalSize (cell : Group → Child → ℝ) : ℝ := ∑ g, groupSize cell g

/-- Destination entropy within one group, multiplied by that group's size. -/
noncomputable def groupEntropy (cell : Group → Child → ℝ) (g : Group) : ℝ :=
  ∑ c, cell g c * Real.log (groupSize cell g / cell g c)

/-- Destination entropy after the group identity is forgotten, multiplied by
the total number of labels. -/
noncomputable def childEntropy (cell : Group → Child → ℝ) : ℝ :=
  ∑ c, childSize cell c * Real.log (totalSize cell / childSize cell c)

theorem sum_childSize (cell : Group → Child → ℝ) :
    (∑ c, childSize cell c) = totalSize cell := by
  unfold childSize totalSize groupSize
  rw [Finset.sum_comm]

omit [Fintype Group] in
theorem cell_le_groupSize (cell : Group → Child → ℝ)
    (hnonneg : ∀ g c, 0 ≤ cell g c) (g : Group) (c : Child) :
    cell g c ≤ groupSize cell g := by
  exact Finset.single_le_sum (fun c' _ => hnonneg g c') (Finset.mem_univ c)

/-- One destination's contribution to the conditional-entropy inequality. -/
theorem column_entropy_le (cell : Group → Child → ℝ)
    (hnonneg : ∀ g c, 0 ≤ cell g c) (c : Child) :
    (∑ g, cell g c * Real.log (groupSize cell g / cell g c)) ≤
      childSize cell c * Real.log (totalSize cell / childSize cell c) := by
  exact log_sum_le_mass_ratio Finset.univ (fun g => cell g c) (groupSize cell)
    (fun g _ => hnonneg g c) (fun g _ => cell_le_groupSize cell hnonneg g c)

/-- Conditioning on the group cannot increase the destination entropy.
The statement includes arbitrary zero rows and zero columns. -/
theorem conditional_entropy_le (cell : Group → Child → ℝ)
    (hnonneg : ∀ g c, 0 ≤ cell g c) :
    (∑ g, groupEntropy cell g) ≤ childEntropy cell := by
  unfold groupEntropy childEntropy
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun c _ => column_entropy_le cell hnonneg c

omit [Fintype Group] in
/-- Every group contributes a nonnegative amount of entropy. -/
theorem group_entropy_nonneg (cell : Group → Child → ℝ)
    (hnonneg : ∀ g c, 0 ≤ cell g c) (g : Group) :
    0 ≤ groupEntropy cell g := by
  apply Finset.sum_nonneg
  intro c _hc
  by_cases hp : 0 < cell g c
  · have hratio : 1 ≤ groupSize cell g / cell g c :=
      (one_le_div hp).mpr (cell_le_groupSize cell hnonneg g c)
    exact mul_nonneg hp.le (Real.log_nonneg hratio)
  · have hz : cell g c = 0 := le_antisymm (le_of_not_gt hp) (hnonneg g c)
    simp [hz]

omit [Fintype Group] in
/-- If no destination receives more than `r` labels from a group, that group
spends at least its size times `log (size / r)`. -/
theorem group_entropy_lower_bound (cell : Group → Child → ℝ)
    (hnonneg : ∀ g c, 0 ≤ cell g c) (g : Group) (r : ℝ) (hr : 0 < r)
    (hcap : ∀ c, cell g c ≤ r) :
    groupSize cell g * Real.log (groupSize cell g / r) ≤ groupEntropy cell g := by
  unfold groupEntropy
  rw [groupSize, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _hc
  by_cases hp : 0 < cell g c
  · have hG : 0 < groupSize cell g :=
      lt_of_lt_of_le hp (cell_le_groupSize cell hnonneg g c)
    have hratio : groupSize cell g / r ≤ groupSize cell g / cell g c := by
      apply (div_le_div_iff₀ hr hp).mpr
      exact mul_le_mul_of_nonneg_left (hcap c) hG.le
    have hlog := Real.log_le_log (div_pos hG hr) hratio
    exact mul_le_mul_of_nonneg_left hlog hp.le
  · have hz : cell g c = 0 := le_antisymm (le_of_not_gt hp) (hnonneg g c)
    simp [hz]

/-- Selected groups may be bounded while all other groups are left in the
array. Their entropy is nonnegative and therefore cannot invalidate the
budget for the selected groups. -/
theorem selected_group_entropy_le (cell : Group → Child → ℝ)
    (hnonneg : ∀ g c, 0 ≤ cell g c) (selected : Finset Group) :
    (∑ g ∈ selected, groupEntropy cell g) ≤ childEntropy cell := by
  have hsubset : selected ⊆ Finset.univ := Finset.subset_univ _
  have hsum : (∑ g ∈ selected, groupEntropy cell g) ≤ ∑ g, groupEntropy cell g :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun g _ _ => group_entropy_nonneg cell hnonneg g)
  exact hsum.trans (conditional_entropy_le cell hnonneg)

/-- The entropy spent by disjoint selected groups of a common size `h`, with
at most `r` labels per destination. The array explicitly accounts for all
labels, including those in groups which are not selected. -/
theorem selected_group_budget (cell : Group → Child → ℝ)
    (hnonneg : ∀ g c, 0 ≤ cell g c) (selected : Finset Group)
    (h r : ℝ) (hr : 0 < r)
    (hsize : ∀ g ∈ selected, groupSize cell g = h)
    (hcap : ∀ g ∈ selected, ∀ c, cell g c ≤ r) :
    ((selected.card : ℝ) * h) * Real.log (h / r) ≤ childEntropy cell := by
  have hlocal (g : Group) (hg : g ∈ selected) :
      h * Real.log (h / r) ≤ groupEntropy cell g := by
    simpa only [hsize g hg] using
      group_entropy_lower_bound cell hnonneg g r hr (hcap g hg)
  have hsum := Finset.sum_le_sum hlocal
  have hselected := selected_group_entropy_le cell hnonneg selected
  have hleft : (∑ _g ∈ selected, h * Real.log (h / r)) =
      ((selected.card : ℝ) * h) * Real.log (h / r) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hleft] at hsum
  exact hsum.trans hselected

/-- Dividing the selected-group entropy budget by its positive per-label
price bounds the number of labels in those groups. For paths set `r = 1`;
for scale groups set `r = 2`.
-/
theorem selected_label_count_le (cell : Group → Child → ℝ)
    (hnonneg : ∀ g c, 0 ≤ cell g c) (selected : Finset Group)
    (h r : ℝ) (hr : 0 < r) (hseparated : r < h)
    (hsize : ∀ g ∈ selected, groupSize cell g = h)
    (hcap : ∀ g ∈ selected, ∀ c, cell g c ≤ r) :
    (selected.card : ℝ) * h ≤ childEntropy cell / Real.log (h / r) := by
  have hlog : 0 < Real.log (h / r) :=
    Real.log_pos ((one_lt_div hr).mpr hseparated)
  apply (le_div_iff₀ hlog).mpr
  exact selected_group_budget cell hnonneg selected h r hr hsize hcap

end Array

end SortingAdversary.Optimal.GroupEntropy
