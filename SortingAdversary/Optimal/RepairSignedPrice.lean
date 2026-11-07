import SortingAdversary.Optimal.RepairPricing

/-!
# Signed prices of actual immutable hub histories

Concrete repair summaries supply the records; final node states supply the
unchanged immutable decoder. Largest blocks are computed by the existing
`HubPricing.largestAt`, rather than supplied as maxima. Only the elementary
per-child population bound is needed by the global code argument.
-/

namespace SortingAdversary.Optimal.RepairPricing

open scoped BigOperators
open WidthRepair StructuralNormalize StableBatches HubSelector BatchWindows HubPricing

variable {n : ℕ}

def scaleCount (events : List (HubEvent n)) : ℕ := (events.filter (fun e => e.scale)).length

theorem sum_prices (p : Parameters) (M : ℕ) (events : List (HubEvent n)) :
    (events.map (HubEvent.price p M)).sum =
      (events.map (HubEvent.unitPrice M)).sum +
        scaleCount events * Real.log (2 * (4 : ℝ) ^ p.scale.width.B) := by
  induction events with
  | nil => simp [scaleCount]
  | cons e rest ih =>
    cases hs : e.scale <;> simp [HubEvent.price, scaleCount, hs, ih, add_mul, add_assoc, add_left_comm, add_comm]

namespace GlobalHistory

variable {Node : Type*} [DecidableEq Node] {H : ℕ}

abbrev Events (Node : Type*) (n H : ℕ) := Fin H → Node × HubEvent n

def destinations (events : Events Node n H) : Finset (Node × ℕ) :=
  Finset.univ.image (fun i => ((events i).1, (events i).2.identity))

def countAt (events : Events Node n H) (c : Node × ℕ) : ℕ :=
  (Finset.univ.filter (fun i => ((events i).1, (events i).2.identity) = c)).card

def pastEvents (final : Node → State n) (exponent : Node → ℕ) (events : Events Node n H)
    (fits : ∀ i, (events i).2.Fits (final (events i).1))
    (cap : ∀ v, (final v).pool.palette + 1 ≤ 2 ^ exponent v) :
    Fin H → GlobalPastBlock exponent :=
  fun i => ⟨(events i).1, (events i).2.past _ ((fits i).births.trans (cap _))⟩

theorem pastEvents_destination (final : Node → State n) (exponent : Node → ℕ) (events : Events Node n H)
    (fits : ∀ i, (events i).2.Fits (final (events i).1))
    (cap : ∀ v, (final v).pool.palette + 1 ≤ 2 ^ exponent v) (i : Fin H) :
    HubPricing.destination (fun v => paletteRank (final v).order)
      (fun v => paletteRank_injective (final v).order) (pastEvents final exponent events fits cap i) =
        ((events i).1, (events i).2.identity) := by
  change ((events i).1, hubColour (paletteRank (final (events i).1).order)
    (paletteRank_injective (final (events i).1).order) (events i).2.block) = _
  rw [(fits i).decoder]

theorem pastEvents_destinations (final : Node → State n) (exponent : Node → ℕ) (events : Events Node n H)
    (fits : ∀ i, (events i).2.Fits (final (events i).1))
    (cap : ∀ v, (final v).pool.palette + 1 ≤ 2 ^ exponent v) :
    HubPricing.destinations (fun v => paletteRank (final v).order)
      (fun v => paletteRank_injective (final v).order) (pastEvents final exponent events fits cap) =
        destinations events := by
  unfold HubPricing.destinations destinations
  simp only [pastEvents_destination]

theorem pastEvents_count (final : Node → State n) (exponent : Node → ℕ) (events : Events Node n H)
    (fits : ∀ i, (events i).2.Fits (final (events i).1))
    (cap : ∀ v, (final v).pool.palette + 1 ≤ 2 ^ exponent v) (c : Node × ℕ) :
    HubPricing.countAt (fun v => paletteRank (final v).order)
      (fun v => paletteRank_injective (final v).order) (pastEvents final exponent events fits cap) c =
        countAt events c := by
  unfold HubPricing.countAt countAt
  simp only [pastEvents_destination]

/-- The global signed debit is a theorem about the actual immutable
identities in the emitted history. The maximum block and dictionary decoder
are computed from these records inside the proof. -/
theorem signed_debit_le [Fintype Node] [Nonempty Node]
    (final : Node → State n) (exponent : Node → ℕ) (events : Events Node n H)
    (fits : ∀ i, (events i).2.Fits (final (events i).1))
    (cap : ∀ v, (final v).pool.palette + 1 ≤ 2 ^ exponent v)
    (population : ∀ c ∈ destinations events, countAt events c ≤ 2 ^ exponent c.1) :
    (∑ i : Fin H, (events i).2.unitPrice (exponent (events i).1)) -
      (∑ c ∈ destinations events, Real.log ((countAt events c).factorial : ℝ)) ≤
      SignedPrice.priceCoefficient (Real.exp 1 * 128) *
        SignedPrice.entropyEnvelope H
          ((DyadicDictionary.totalCapacity exponent : ℝ) +
            ∑ c ∈ destinations events, (countAt events c : ℝ) *
              Real.log ((2 : ℝ) ^ exponent c.1 / countAt events c)) := by
  classical
  let v : Node := Classical.choice inferInstance
  let chosen := OrdinaryPromotion.singletonBlock (final v).order ⟨0, Nat.succ_pos _⟩
  let fallback : GlobalPastBlock exponent :=
    ⟨v, ⟨(final v).pool.palette + 1, cap v, chosen.val,
      OrdinaryPromotion.singletonBlock_available (final v).order ⟨0, Nat.succ_pos _⟩⟩⟩
  have h := HubPricing.history_signed_debit_le
    (fun v => paletteRank (final v).order) (fun v => paletteRank_injective (final v).order)
    (pastEvents final exponent events fits cap) fallback 128 (by norm_num) (by
      intro c hc
      rw [pastEvents_destinations] at hc
      rw [pastEvents_count]
      exact_mod_cast population c hc)
  simpa only [pastEvents_destinations, pastEvents_count, HubPricing.unitPrice,
    pastEvents, HubEvent.past, HubEvent.unitPrice] using h

end GlobalHistory

namespace Summary

variable {p : Parameters} {s t : State n} {trace : Trace s t}

/-- Scalar charges of an actual summary separate into ordinary dictionary
prices, cheap pins, cuts and the explicit number of scale surcharges. -/
theorem priced_separated (summary : Summary p trace) (M : ℕ)
    (hcap : t.pool.palette + 1 ≤ 2 ^ M) :
    logCharge trace ≤
      summary.cheap * Real.log (p.scale.width.cheapCharge : ℝ) +
      summary.cuts * Real.log (p.scale.width.cutCharge : ℝ) +
      (summary.hubs.map (HubEvent.unitPrice M)).sum +
      scaleCount summary.hubs * Real.log (2 * (4 : ℝ) ^ p.scale.width.B) := by
  have h := summary.priced M hcap
  unfold totalPrice at h
  rw [sum_prices] at h
  simpa only [add_assoc] using h

end Summary

end SortingAdversary.Optimal.RepairPricing
