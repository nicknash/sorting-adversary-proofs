import SortingAdversary.Continuous.TraceAccounting
import SortingAdversary.Continuous.RefinementBatch
import SortingAdversary.Continuous.TreeRouting

/-!
# Local geometric guarantees for the concrete accounting trace

The trace reads its gains from actual volumes. These lemmas translate the
density and answer-probability guarantees of the finite routines into the
local predicates consumed by `TraceAccounting.run_initial_prefix`.
-/

namespace SortingAdversary.Continuous.TraceAccounting

noncomputable section

open FiniteAveraging OrderRegion TreeState Density MeasureTheory

variable {n : ℕ}

theorem Move.gain_eq_log_density (m : Move n) (s : State n ℝ)
    (hxx : s.system.edge m.item m.item = false)
    (hc : s.system.lower m.item < (m.anchor.coordinate : ℝ) ∧
      (m.anchor.coordinate : ℝ) < s.system.upper m.item)
    (hV : 0 < nodeVolume s.system)
    (hf : 0 < density s.system m.item (m.anchor.coordinate : ℝ)) :
    m.gain s = log2 (density s.system m.item (m.anchor.coordinate : ℝ)) := by
  unfold Move.gain Move.apply TreeState.normalize
  rw [normalize_nodeVolume, refineAt_volume_identity s m.item _ hxx hc hV,
    log2_mul (ne_of_gt hV) (ne_of_gt hf)]
  ring

theorem Move.gain_eq_log_density_of_positive (m : Move n) (s : State n ℝ)
    (hxx : s.system.edge m.item m.item = false)
    (hc : s.system.lower m.item < (m.anchor.coordinate : ℝ) ∧
      (m.anchor.coordinate : ℝ) < s.system.upper m.item)
    (hV : 0 < nodeVolume s.system) (hV' : 0 < nodeVolume (m.apply s).system) :
    m.gain s = log2 (density s.system m.item (m.anchor.coordinate : ℝ)) := by
  have hm := refineAt_volume_identity s m.item (m.anchor.coordinate : ℝ) hxx hc hV
  have hp : 0 < nodeVolume s.system * density s.system m.item (m.anchor.coordinate : ℝ) := by
    simpa only [Move.apply, TreeState.normalize, normalize_nodeVolume, hm] using hV'
  exact m.gain_eq_log_density s hxx hc hV ((mul_pos_iff_of_pos_left hV).mp hp)

theorem valid_selection_of_density {k : ℕ} (F : Frame n) (m : Move n)
    (hxx : F.state.system.edge m.item m.item = false)
    (hc : F.state.system.lower m.item < (m.anchor.coordinate : ℝ) ∧
      (m.anchor.coordinate : ℝ) < F.state.system.upper m.item)
    (hV : 0 < nodeVolume F.state.system)
    (hf : 0 < density F.state.system m.item (m.anchor.coordinate : ℝ))
    (hg : (k : ℝ) < log2 (density F.state.system m.item (m.anchor.coordinate : ℝ)))
    (ht : stopMass k * m.anchor.1 - 4 ≤
      log2 (density F.state.system m.item (m.anchor.coordinate : ℝ))) :
    (Action.selection m).Valid k F := by
  change (k : ℝ) < m.gain F.state ∧ stopMass k * m.anchor.1 - 4 ≤ m.gain F.state
  rw [m.gain_eq_log_density F.state hxx hc hV hf]
  exact ⟨hg, ht⟩

theorem valid_degree_of_density {k : ℕ} (F : Frame n) (m : Move n)
    (hxx : F.state.system.edge m.item m.item = false)
    (hc : F.state.system.lower m.item < (m.anchor.coordinate : ℝ) ∧
      (m.anchor.coordinate : ℝ) < F.state.system.upper m.item)
    (hV : 0 < nodeVolume F.state.system)
    (hf : 0 < density F.state.system m.item (m.anchor.coordinate : ℝ))
    (ht : stopMass k * m.anchor.1 - 4 ≤
      log2 (density F.state.system m.item (m.anchor.coordinate : ℝ)))
    (hd : k ≤ (ArcBudget.incident F.state.system m.item).card) :
    (Action.degree m).Valid k F := by
  change (stopMass k * m.anchor.1 - 4 ≤ m.gain F.state) ∧ _
  rw [m.gain_eq_log_density F.state hxx hc hV hf]
  exact ⟨ht, hd⟩

theorem tariff_of_central {k : ℕ} (hk : 0 < k) (c : DyadicAnchor) {g : ℝ}
    (hg : (c.1 : ℝ) - 4 < g) : stopMass k * c.1 - 4 ≤ g := by
  have hs : stopMass k ≤ 1 := (stopMass_lt_one (by exact_mod_cast hk)).le
  have hm := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg c.1 : (0 : ℝ) ≤ c.1)
  linarith

theorem valid_answer_of_retained {k : ℕ} (hk : 64 ≤ k) (F : Frame n)
    (q : Query n) (a : Answer) (order : List (Fin n))
    (hV : 0 < nodeVolume F.state.system)
    (hret : answerRetained k * nodeVolume F.state.system ≤
      nodeVolume (record F.state q a).system) :
    (Action.answer q a order).Valid k F := by
  have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < answerRetained k := by linarith [(answerRetained_bounds hkR).1]
  have hlog := log2_mono (mul_pos hp hV) hret
  rw [log2_mul (ne_of_gt hp) (ne_of_gt hV)] at hlog
  change log2 (nodeVolume F.state.system) -
    log2 (nodeVolume (TreeState.normalize (record F.state q a) order).system) ≤ answerLoss k
  simp only [TreeState.normalize, normalize_nodeVolume]
  unfold answerLoss
  linarith

theorem valid_answer_of_probability {k : ℕ} (hk : 64 ≤ k) (F : Frame n)
    (q : Query n) (a : Answer) (order : List (Fin n))
    (hr : (route (F.state.location q.left) (F.state.location q.right)).AnchorAnswer a)
    (hV : 0 < nodeVolume F.state.system)
    (hp : answerRetained k ≤ (uniformMeasure F.state.system).real
      {X | (route (F.state.location q.left) (F.state.location q.right)).Holds
        (X q.left) (X q.right) a}) :
    (Action.answer q a order).Valid k F :=
  valid_answer_of_retained hk F q a order hV
    (record_volume_retention F.state q a hr hV (answerRetained k) hp)

theorem gainsAt_eq_zero (rs : List (DyadicAnchor × ℝ)) (c : DyadicAnchor)
    (hc : c ∉ rs.map Prod.fst) : gainsAt rs c = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hn : c ≠ r.1 ∧ c ∉ rs.map Prod.fst := by simpa using hc
    simp [gainsAt, hn.1, ih hn.2]

theorem gainsAt_eq_of_mem (rs : List (DyadicAnchor × ℝ))
    (hn : (rs.map Prod.fst).Nodup) (c : DyadicAnchor) (g : ℝ) (hc : (c, g) ∈ rs) :
    gainsAt rs c = g := by
  induction rs with
  | nil => simp at hc
  | cons r rs ih =>
    have hn' : r.1 ∉ rs.map Prod.fst ∧ (rs.map Prod.fst).Nodup := by simpa using hn
    rcases List.mem_cons.mp hc with he | he
    · cases he
      simp [gainsAt, gainsAt_eq_zero rs c hn'.1]
    · have hcd : c ≠ r.1 := by
        intro hcd
        apply hn'.1
        rw [← hcd]
        exact List.mem_map.mpr ⟨(c, g), he, rfl⟩
      simp [gainsAt, hcd, ih hn'.2 he]

theorem valid_path_of_tariffs {k : ℕ} (F : Frame n) (ms : List (Move n))
    (hn : (ms.map Move.anchor).Nodup) (hl : ms.length = 2 ^ k)
    (ht : ∀ r ∈ gainRecords F.state ms, stopMass k * r.1.1 - 4 ≤ r.2) :
    (Action.path ms).Valid k F := by
  refine ⟨hn, ?_, ?_⟩
  · change (ms.map Move.anchor).toFinset.card = _
    rw [List.toFinset_card_of_nodup hn, List.length_map, hl]
  · intro c hc
    change c ∈ (ms.map Move.anchor).toFinset at hc
    have hcm : c ∈ (gainRecords F.state ms).map Prod.fst := by
      rw [gainRecords_anchors]
      exact List.mem_toFinset.mp hc
    obtain ⟨r, hr, hrc⟩ := List.mem_map.mp hcm
    obtain ⟨d, g⟩ := r
    dsimp at hrc
    subst d
    change stopMass k * c.1 - 4 ≤ gainsAt (gainRecords F.state ms) c
    rw [gainsAt_eq_of_mem _ (by simpa only [gainRecords_anchors] using hn) c g hr]
    exact ht (c, g) hr

end
end SortingAdversary.Continuous.TraceAccounting
