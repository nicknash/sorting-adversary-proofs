import SortingAdversary.Continuous.PolylogCompareLoops
import SortingAdversary.Continuous.PolylogMoveProof
import SortingAdversary.Continuous.PolylogRecordProof

/-!
# Stored comparison at the scheduled binary precision

The invariant counts individual committed moves. The selection can commit
at most two, recording commits none, and the longest reserved path has
exactly the controller's prescribed length. These local allowances cover
every intermediate allocator and every fallback prefix probe.
-/

namespace SortingAdversary.Continuous.PolylogCompare

open Controller (totalDepth horizon Ready Admissible)
open PolylogResources (tableHeight)
open Optimal.Parameters (logCap)
open PolylogAdversary (parameter extra)
open ArbitraryLabels (pathHeight)
attribute [local instance] PolylogOracle.choices PolylogOracle.choices_valid

abbrev binaryPoint (n : ℕ) := PolylogSchedule.capacity (logCap n) (pathHeight (parameter n)) n
abbrev ScheduledMemory (n : ℕ) := Memory n (tableHeight n) (binaryPoint n).size
abbrev Tracks {n : ℕ} := @Aligned n (tableHeight n) (binaryPoint n).size (binaryPoint n) (logCap n)
abbrev depthLimit (n : ℕ) := horizon n + 2 ^ parameter n + 2

theorem binaryPoint_short (n : ℕ) : logCap n ≤ binaryPoint n := by
  unfold binaryPoint PolylogSchedule.capacity
  omega

theorem depthLimit_room {n d : ℕ} (hd : d ≤ depthLimit n) :
    logCap n + 2*d + 2 ≤ binaryPoint n := by
  have hk : 2^parameter n ≤ pathHeight (parameter n) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  dsimp only [binaryPoint,PolylogSchedule.capacity,depthLimit] at *
  nlinarith [Nat.zero_le ((horizon n)*(pathHeight (parameter n)))]

theorem depthLimit_table {n : ℕ} (hk : 64 ≤ parameter n) :
    depthLimit n ≤ horizon n + logCap n+2 := by
  have h := PolylogSchedule.height_le (extra := extra) hk
  have h' : 2^parameter n ≤ pathHeight (parameter n) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  change pathHeight (parameter n) ≤ logCap n at h
  exact Nat.add_le_add_right (Nat.add_le_add_left (h'.trans h) _) _

theorem select_step_aligned {n : ℕ} (hk : 64 ≤ parameter n) (q : Query n)
    (m : ScheduledMemory n) (M : Controller.Memory n) (hs : Tracks m M)
    (ready : Ready (parameter n) M) (hm : totalDepth M ≤ depthLimit n) (x : Fin n)
    (part : PolylogOracle.attempt M (parameter n) q = .refine x (PolylogOracle.prefixAnchor M x)) :
    Tracks (move (parameter n) m x (writePrefix (binaryPoint n) m x)).value
      (Controller.applyMove M (Controller.makeMove M x (PolylogOracle.prefixAnchor M x))) := by
  obtain ⟨nodes,hmr⟩ := hs.storage
  have spec := PolylogOracle.attempt_refine_spec M _ hk ready.admissible q x _ part
  exact move_aligned_value _ _ hs ready.admissible
    (PolylogSchedule.capacity_bits (extra := extra) hk le_rfl)
    (hm.trans (depthLimit_table hk)) x _ _ (prefix_value hmr ready.toGeometric hs.grid
      (depthLimit_room hm) (Nat.lt_size_self _) x) (prefix_growth ..)
    ⟨spec.2.2.1,spec.2.2.2.1⟩ (PolylogPrecision.prefix_grid M ready.toGeometric hs.grid x)

theorem repair_step_aligned {n : ℕ} (hk : 64 ≤ parameter n)
    (m : ScheduledMemory n) (M : Controller.Memory n) (hs : Tracks m M)
    (adm : Admissible (parameter n) M) (hm : totalDepth M ≤ depthLimit n) (x : Fin n)
    (he : (candidate (binaryPoint n) (parameter n) m x).value =
      (PolylogOracle.centralTest M (parameter n) x).map Certificates.roundUp) :
    Tracks (repairMove (binaryPoint n) (parameter n) m x).value
      (Controller.applyMove M (Controller.makeMove M x (PolylogOracle.anchor M (parameter n) x))) := by
  obtain ⟨nodes,hmr⟩ := hs.storage
  let t := (candidate (binaryPoint n) (parameter n) m x).value
  have spec := PolylogOracle.anchor_move_spec M _ hk adm x
  have grid : FiniteAveraging.OnDyadicGrid (logCap n+2*totalDepth M+2)
      (PolylogOracle.anchor M (parameter n) x) := by
    cases hc : PolylogOracle.centralTest M (parameter n) x with
    | none =>
      simpa only [PolylogOracle.anchor,hc] using PolylogPrecision.prefix_grid M adm.toGeometric hs.grid x
    | some J =>
      simp only [PolylogOracle.anchor,hc]
      exact Precision.grid_mono (PolylogPrecision.scheduled_central extra hk M adm x J hc) (by omega)
  exact move_aligned_value _ _ hs adm (PolylogSchedule.capacity_bits (extra := extra) hk le_rfl)
    (hm.trans (depthLimit_table hk)) x (mint (binaryPoint n) m x t) _
    (mint_value extra hmr hk adm hs.grid (depthLimit_room hm) (Nat.lt_size_self _)
      (binaryPoint_short n) x t he) (mint_growth ..) ⟨spec.2.1,spec.2.2.1⟩ grid

/-- Compose the two prepared-test readback theorems with the actual allocator,
stored graph update, reserved-path search and loop implementations. -/
theorem compare_simulation {n : ℕ} (hk : 64 ≤ parameter n)
    (test : ∀ (m : ScheduledMemory n) M, Tracks m M → Ready (parameter n) M → ∀ q,
      (check (binaryPoint n) (parameter n) m q).value.realize M =
        PolylogOracle.attempt M (parameter n) q)
    (central : ∀ (m : ScheduledMemory n) M, Tracks m M → Admissible (parameter n) M → ∀ x,
      (candidate (binaryPoint n) (parameter n) m x).value =
        (PolylogOracle.centralTest M (parameter n) x).map Certificates.roundUp)
    (m : ScheduledMemory n) (M : Controller.Memory n) (ready : Ready (parameter n) M)
    (rep : Tracks m M) (hm : totalDepth M ≤ horizon n) (q : Query n) :
    let r := (PolylogAdversary.policy n).compare (parameter n) M q
    ∃ u, (compare (binaryPoint n) (parameter n) m q).value = some (u,r.answer) ∧ Tracks u r.memory := by
  let k := parameter n
  let D := binaryPoint n
  obtain ⟨s,hs⟩ := Controller.selectLoop_total k hk q M ready
  obtain ⟨u,hu,hrep,hdepth⟩ := select_simulates Tracks (B := depthLimit n) hk q
    (fun p N r a _ => test p N r a q) (select_step_aligned hk q) 3 m M rep ready
    (Nat.add_le_add_right (hm.trans (Nat.le_add_right ..)) 2) hs
  have sel := Controller.selectLoop_spec k hk q 3 M ready s hs
  have hp := PolylogOracle.attempt_answer_probability s.memory k (by omega)
    sel.1.toGeometric q s.answer sel.2.1
  let N := Controller.recorded s.memory q s.answer
  have post : Admissible k N := sel.1.recordedAdmissible q s.answer
    (sel.1.toGeometric.recorded hk q s.answer hp.1 hp.2)
  let z := (record k u q s.answer).value
  let xs := (PolylogRepair.choose z.1.spatial.graph k z.2).value
  have stored : Tracks z.1 N := record_aligned hrep sel.1 (PolylogResources.label_fits n) q s.answer post
  have eq : xs = PolylogRepair.reserved N.tree.system.edge k :=
    record_choose_aligned hrep sel.1 (PolylogResources.label_fits n) q s.answer post
  have length : xs.length ≤ 2^k := eq ▸ reserved_length N k
  have depth : totalDepth N = totalDepth s.memory := rfl
  have cap : totalDepth N + xs.length ≤ depthLimit n := by
    change xs.length ≤ 2^parameter n at length
    dsimp only [depthLimit]
    omega
  have after := repairList_simulates Tracks hk
    (fun p T tr adm room x => repair_step_aligned hk p T tr adm room x (central p T tr adm x))
    xs z.1 N stored post cap
  let out := (repairList D k xs z.1).value
  have repaired : Tracks out (Controller.repair k N).1 := by
    rw [← reserved_repair, ← eq]
    exact after
  let ans := (PolylogAdversary.policy n).compare k M q
  have answer : ans.answer = s.answer := by
    simp only [ans,PolylogAdversary.policy,Controller.compare,hs,Option.map_some,Option.getD_some]
  have memory : ans.memory = (Controller.repair k N).1 := by
    simp only [ans,PolylogAdversary.policy,Controller.compare,hs,Option.map_some,Option.getD_some]
    rfl
  refine ⟨out, ?_, memory ▸ repaired⟩
  change (compare D k m q).value = some (out,ans.answer)
  rw [answer]
  change (select D k q 3 m).value = some (u,s.answer) at hu
  simp only [compare,hu]
  rfl

end SortingAdversary.Continuous.PolylogCompare
