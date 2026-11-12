import SortingAdversary.Continuous.InducedEnclosure
import SortingAdversary.Continuous.CertificateSuccess

/-!
# The finite retained graph used by the local routines

The radius is computed from the paper's certificate parameters. Only the
induced retained graph is topologically sorted. Interior vertices are swept;
the one additional layer supplies every conditional-boundary value needed by
those updates. All indices are computably related to the original labels.
-/

namespace SortingAdversary.Continuous.Neighborhood

open FiniteAveraging OrderRegion GraphOrder EnclosureParameters CertificateSuccess
open InducedEnclosure MeasureTheory Set
open SortingAdversary.Optimal.GraphBalls

variable {n : ℕ}

def sweeps (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w) : ℕ :=
  sweepCount k H (accuracy k (neighborhoodBound k H) w) (failure k)
    (accuracy_pos hk _ hw) (failure_pos hk)

def labels (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : Finset (Fin n)) : Finset (Fin n) :=
  retained D Q (H * sweeps k H hk w hw + 1)

def raw (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : Finset (Fin n)) : System (Fin (labels D k H hk w hw Q).card) ℚ :=
  induced D (label (labels D k H hk w hw Q))

def embedding (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : Finset (Fin n)) : Fin (labels D k H hk w hw Q).card ↪ Fin n :=
  (orderEquiv (raw D k H hk w hw Q)).toEmbedding.trans (label (labels D k H hk w hw Q))

def system (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : Finset (Fin n)) : System (Fin (labels D k H hk w hw Q).card) ℚ :=
  induced D (embedding D k H hk w hw Q)

def query (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : Finset (Fin n)) (x : Fin n) (hx : x ∈ Q) : Fin (labels D k H hk w hw Q).card :=
  (orderEquiv (raw D k H hk w hw Q)).symm
    (localIndex (labels D k H hk w hw Q) x (query_mem_retained D Q _ x hx))

def queries (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : Finset (Fin n)) : Finset (Fin (labels D k H hk w hw Q).card) :=
  Finset.univ.filter fun x => embedding D k H hk w hw Q x ∈ Q

def schedule (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
    (Q : Finset (Fin n)) : List (Fin (labels D k H hk w hw Q).card) :=
  certificateSchedule (system D k H hk w hw Q) k H (neighborhoodBound k H) hk w hw
    (queries D k H hk w hw Q)

variable (D : System (Fin n) ℚ) (k H : ℕ) (hk : 0 < k) (w : ℚ) (hw : 0 < w)
  (Q : Finset (Fin n))

theorem system_eq_indexed : system D k H hk w hw Q = indexed (raw D k H hk w hw Q) := rfl

@[simp] theorem embedding_query (x : Fin n) (hx : x ∈ Q) :
    embedding D k H hk w hw Q (query D k H hk w hw Q x hx) = x := by
  simp only [embedding, query, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply]
  exact label_localIndex _ x _

@[simp] theorem lower_query (x : Fin n) (hx : x ∈ Q) :
    (system D k H hk w hw Q).lower (query D k H hk w hw Q x hx) = D.lower x := by
  simp only [system, induced, embedding_query]

@[simp] theorem upper_query (x : Fin n) (hx : x ∈ Q) :
    (system D k H hk w hw Q).upper (query D k H hk w hw Q x hx) = D.upper x := by
  simp only [system, induced, embedding_query]

theorem range_embedding : Set.range (embedding D k H hk w hw Q) = labels D k H hk w hw Q := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact label_mem _ _
  · intro hx
    refine ⟨(orderEquiv (raw D k H hk w hw Q)).symm (localIndex _ x hx), ?_⟩
    simp only [embedding, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.apply_symm_apply, label_localIndex]

@[simp] theorem mem_queries (x : Fin (labels D k H hk w hw Q).card) :
    x ∈ queries D k H hk w hw Q ↔ embedding D k H hk w hw Q x ∈ Q := by
  simp [queries]

theorem queries_card : (queries D k H hk w hw Q).card ≤ Q.card := by
  have hsub : (queries D k H hk w hw Q).image (embedding D k H hk w hw Q) ⊆ Q := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_queries D k H hk w hw Q y).mp hy
  calc
    _ = ((queries D k H hk w hw Q).image (embedding D k H hk w hw Q)).card :=
      (Finset.card_image_of_injective _ (embedding D k H hk w hw Q).injective).symm
    _ ≤ Q.card := Finset.card_le_card hsub

theorem queries_pair (x y : Fin n) :
    queries D k H hk w hw {x, y} =
      {query D k H hk w hw {x, y} x (by simp), query D k H hk w hw {x, y} y (by simp)} := by
  ext z
  simp only [mem_queries, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (hx | hy)
    · exact Or.inl ((embedding D k H hk w hw {x, y}).injective
        (hx.trans (embedding_query D k H hk w hw {x, y} x (by simp)).symm))
    · exact Or.inr ((embedding D k H hk w hw {x, y}).injective
        (hy.trans (embedding_query D k H hk w hw {x, y} y (by simp)).symm))
  · rintro (rfl | rfl)
    · exact Or.inl (embedding_query D k H hk w hw {x, y} x (by simp))
    · exact Or.inr (embedding_query D k H hk w hw {x, y} y (by simp))

theorem queries_singleton (x : Fin n) :
    queries D k H hk w hw {x} = {query D k H hk w hw {x} x (by simp)} := by
  ext z
  simp only [mem_queries, Finset.mem_singleton]
  constructor
  · intro hz
    exact (embedding D k H hk w hw {x}).injective
      (hz.trans (embedding_query D k H hk w hw {x} x (by simp)).symm)
  · rintro rfl
    exact embedding_query D k H hk w hw {x} x (by simp)

theorem normalized (hD : Normalized D.toReal) : Normalized (system D k H hk w hw Q).toReal :=
  induced_normalized D.toReal _ hD

theorem volume_pos (hV : 0 < volume (region D.toReal)) :
    0 < volume (region (system D k H hk w hw Q).toReal) :=
  induced_volume_pos D.toReal _ hV

theorem degree (hdegree : ∀ x, (neighbors D.edge x).card ≤ k) :
    ∀ x, (neighbors (system D k H hk w hw Q).edge x).card ≤ k :=
  fun x => (neighbors_induced_card D _ x).trans (hdegree _)

theorem ordered (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y) :
    ∀ x y, (system D k H hk w hw Q).edge x y = true → x.val < y.val := by
  rw [system_eq_indexed]
  exact indexed_order (raw D k H hk w hw Q) (fun x => rank (label _ x))
    (fun x y h => hrank _ _ h)

theorem comparable_bound (rank : Fin n → ℕ)
    (hrank : ∀ x y, D.edge x y = true → rank x < rank y)
    (hheight : ∀ x, rank x + 1 ≤ H)
    (hdegree : ∀ x, (neighbors D.edge x).card ≤ k)
    (x : Fin (labels D k H hk w hw Q).card) :
    ComparableDensity.comparableCount (system D k H hk w hw Q).toReal x ≤ neighborhoodBound k H :=
  ComparableBound.comparableCount_toReal_le (system D k H hk w hw Q)
    (fun x => rank (embedding D k H hk w hw Q x)) H k
    (fun x y h => hrank _ _ h) (fun x => hheight _) (degree D k H hk w hw Q hdegree) x

private theorem mem_repeatSchedule {α : Type*} (L : List α) (t : ℕ) (x : α)
    (hx : x ∈ repeatSchedule L t) : x ∈ L := by
  induction t with
  | zero => simp [repeatSchedule] at hx
  | succ t ih =>
    rcases List.mem_append.mp hx with h | h
    · exact ih h
    · exact h

theorem schedule_closed (x : Fin (labels D k H hk w hw Q).card)
    (hx : x ∈ schedule D k H hk w hw Q) : ClosedAt D (embedding D k H hk w hw Q) x := by
  have hint : x ∈ queryInterior (system D k H hk w hw Q) (queries D k H hk w hw Q)
      H (sweeps k H hk w hw) := by
    have hm := mem_repeatSchedule _ _ x hx
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  obtain ⟨q, hq, hxq⟩ := Finset.mem_biUnion.mp hint
  have hq' := (mem_queries D k H hk w hw Q q).mp hq
  have hxq' : embedding D k H hk w hw Q x ∈ ball D.edge (embedding D k H hk w hw Q q)
      (H * sweeps k H hk w hw) :=
    ball_induced_subset D (embedding D k H hk w hw Q) q _ (Finset.mem_image.mpr ⟨x, hxq, rfl⟩)
  intro y hy
  rw [range_embedding]
  refine Finset.mem_biUnion.mpr ⟨embedding D k H hk w hw Q q, hq',
    mem_ball_add D.edge hxq' ?_⟩
  exact (mem_ball_one D.edge _ y).mpr ((mem_closedNeighbors D.edge _ y).mpr (Or.inr hy))

/-- The retained calculation has exactly the same endpoint entries as the
original graph along the embedded local schedule, including multiplicity. -/
theorem enclose_full :
    enclose (system D k H hk w hw Q) (alphabet k H) (schedule D k H hk w hw Q) =
      (enclose D (alphabet k H) ((schedule D k H hk w hw Q).map (embedding D k H hk w hw Q))).map
        (fun I => I ∘ embedding D k H hk w hw Q) :=
  enclose_induced D (embedding D k H hk w hw Q) (alphabet k H) (schedule D k H hk w hw Q)
    (schedule_closed D k H hk w hw Q)

theorem labels_card (hQ : Q.card ≤ 2) (hdegree : ∀ x, (neighbors D.edge x).card ≤ k) :
    (labels D k H hk w hw Q).card ≤
      retainedBound k H (accuracy k (neighborhoodBound k H) w) (failure k)
        (accuracy_pos hk _ hw) (failure_pos hk) := by
  have h := (retained_card D Q k (H * sweeps k H hk w hw + 1) hdegree).trans
    (Nat.mul_le_mul_right ((k + 1) ^ (H * sweeps k H hk w hw + 1)) hQ)
  exact h.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (Nat.le_succ _)))

end SortingAdversary.Continuous.Neighborhood
