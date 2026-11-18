import SortingAdversary.Continuous.PolylogWordWork
import SortingAdversary.Continuous.PolylogCompareWork
import SortingAdversary.Optimal.RationalBitWork

/-!
# Profiled heap writers for the stored comparison

The charged writer returns the identical persistent heap and reference. Its
work includes scalar operations, uniform-cache reads and the dictionary
paths actually taken. A successful central value is converted to an integer
with a binary shift and unsigned division of its reduced components.
-/

namespace SortingAdversary.Continuous.PolylogWordWriter

open PolylogBits PolylogCompare PolylogWordWork
open Optimal.Parameters (logCap)
variable {n b t : ℕ}

def scaledNumerator (q : ℚ) (e : ℕ) : ℕ := (q.num.toNat <<< e) / q.den

theorem scaledNumerator_eq (q : ℚ) (e : ℕ) :
    scaledNumerator q e = PolylogAnchorWrite.numerator q e := by
  by_cases hq : 0 ≤ q
  · have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
    have hcast : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hn
    have eq : q*(2:ℚ)^e = ((q.num.toNat <<< e : ℕ) : ℚ) / q.den := by
      rw [Nat.shiftLeft_eq,Nat.cast_mul,Nat.cast_pow,hcast]
      calc
        _ = ((q.num:ℚ)/q.den)*(2:ℚ)^e := congrArg (fun v : ℚ => v*(2:ℚ)^e) (Rat.num_div_den q).symm
        _ = _ := by push_cast; ring
    rw [PolylogAnchorWrite.numerator,eq,Rat.natFloor_natCast_div_natCast]
    rfl
  · have hz : q.num.toNat = 0 := by
      have hn : ¬0 ≤ q.num := fun e => hq (Rat.num_nonneg.mp e)
      omega
    have hn : q*(2:ℚ)^e ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hq) (by positivity)
    simp [scaledNumerator,hz,PolylogAnchorWrite.numerator,Nat.floor_of_nonpos hn]

/-- The shift and division receive a conservative schoolbook binary charge
at the maximum width of the shifted numerator and the divisor. -/
def scaleWork (q : ℚ) (e : ℕ) := 6*Optimal.RationalBitWork.Model.unit
  (max (q.num.natAbs.size+e+1) q.den.size)

theorem scale_operands (q : ℚ) (e : ℕ) :
    let B := max (q.num.natAbs.size+e+1) q.den.size
    (q.num.toNat <<< e).size ≤ B ∧ q.den.size ≤ B ∧ (scaledNumerator q e).size ≤ B := by
  have habs : q.num.toNat ≤ q.num.natAbs := by cases q.num <;> simp
  have hshift : (q.num.toNat <<< e).size ≤ q.num.natAbs.size+e+1 := by
    by_cases z : q.num.toNat = 0
    · simp [z]
    · rw [Nat.size_shiftLeft z]
      have := Nat.size_le_size habs
      omega
  exact ⟨hshift.trans (le_max_left ..),le_max_right ..,
    (Nat.size_le_size (Nat.div_le_self ..)).trans (hshift.trans (le_max_left ..))⟩

theorem scaleWork_bound {q : ℚ} {e : ℕ} (grid : FiniteAveraging.OnDyadicGrid e q)
    (lo : 0 ≤ q) (hi : q ≤ 1) : scaleWork q e ≤ 54*(e+1)^2 := by
  obtain ⟨hd,hn⟩ := Precision.rational_bits grid lo hi
  have width : max (q.num.natAbs.size+e+1) q.den.size + 1 ≤ 3*(e+1) := by omega
  apply (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left width 2)).trans
  exact le_of_eq (by ring)

def writePrefix (D : ℕ) (m : Memory n t b) (x : Fin n) : WriteResult m :=
  let l := (m.spatial.walls.lower.get x.val).value
  let r := (m.spatial.walls.upper.get x.val).value
  let path := checkedFallbackTrace m.cache.lookup m.heap b D (D-2) l r
  let w := PolylogCompare.writePrefix D m x
  ⟨w.out,4*w.work+(path.run m.heap).work⟩

def mint (D : ℕ) (m : Memory n t b) (x : Fin n) : Option ℚ → WriteResult m
  | none => writePrefix D m x
  | some q =>
    let e := logCap n
    let z := scaledNumerator q e
    let w := PolylogEmbed.embedAddr D e z m.valid m.cache (le_refl b)
    let path := embedTrace m.valid m.cache (le_refl b) (e+1) (D-e) z
    ⟨PolylogAnchorWrite.Written.ofWrite w.toWrite,
      4*(w.work+e+4)+scaleWork q e+(path.run m.heap).work⟩

@[simp] theorem writePrefix_out (D : ℕ) (m : Memory n t b) (x : Fin n) :
    (writePrefix D m x).out = (PolylogCompare.writePrefix D m x).out := rfl

@[simp] theorem mint_out (D : ℕ) (m : Memory n t b) (x : Fin n) (test : Option ℚ) :
    (mint D m x test).out = (PolylogCompare.mint D m x test).out := by
  cases test with
  | none => rfl
  | some q =>
    simp only [mint,PolylogCompare.mint]
    rw [scaledNumerator_eq]

theorem writePrefix_work {n : ℕ} (hk : 64 ≤ PolylogAdversary.parameter n)
    {m : ScheduledMemory n} {M : Controller.Memory n} (align : Tracks m M)
    (depth : Controller.totalDepth M ≤ depthLimit n) (x : Fin n) :
    (writePrefix (binaryPoint n) m x).work ≤ 60000000*(logCap n+1)^4 := by
  let D := binaryPoint n
  let b := D.size
  let L := logCap n+1
  let T := PolylogResources.tableHeight n
  have hb : b ≤ 5+L*3 := PolylogSchedule.capacity_bits (extra := PolylogAdversary.extra) hk le_rfl
  have pos : 1 ≤ L := by dsimp only [L]; omega
  have ht : T ≤ 19*L := by dsimp only [T,PolylogResources.tableHeight,L]; omega
  have hs : Nat.log 2 (D-2) ≤ b :=
    (Nat.log_mono_right (Nat.sub_le D 2)).trans (by
      by_cases z : D = 0
      · simp [z,b]
      · exact (Nat.log_lt_of_lt_pow z (Nat.lt_size_self _)).le)
  have scalar := PolylogCompareWork.prefix_work D m x
  have s : (PolylogCompare.writePrefix D m x).work ≤ 10000*L^2 := by
    apply scalar.trans
    change 8*T+((Nat.log 2 (D-2)+1)*(24*b+20)+(48*b+24))+4 ≤ _
    have u := Nat.mul_le_mul (show Nat.log 2 (D-2)+1 ≤ 9*L by omega) (show 24*b+20 ≤ 216*L by omega)
    nlinarith [Nat.mul_le_mul_right L pos]
  have dp := (stored_prefix_dictionary hk align depth x).2
  have p4 : L^2 ≤ L^4 := Nat.pow_le_pow_right pos (by decide)
  change 4*(PolylogCompare.writePrefix D m x).work+_ ≤ _
  change _ ≤ 50000000*L^4 at dp
  change _ ≤ 60000000*L^4
  omega

theorem mint_work {n : ℕ} (hk : 64 ≤ PolylogAdversary.parameter n)
    {m : ScheduledMemory n} {M : Controller.Memory n} (align : Tracks m M)
    (depth : Controller.totalDepth M ≤ depthLimit n) (adm : Controller.Admissible (PolylogAdversary.parameter n) M)
    (x : Fin n) (test : Option ℚ)
    (he : test = (PolylogOracle.centralTest M (PolylogAdversary.parameter n) x).map Certificates.roundUp) :
    (mint (binaryPoint n) m x test).work ≤ 60000000*(logCap n+1)^4 := by
  rw [he]
  let k := PolylogAdversary.parameter n
  change _ ≤ 60000000*(logCap n+1)^4
  change (mint (binaryPoint n) m x ((PolylogOracle.centralTest M k x).map Certificates.roundUp)).work ≤ _
  cases htest : PolylogOracle.centralTest M k x with
  | none => exact writePrefix_work hk align depth x
  | some J =>
    let q := Certificates.roundUp J
    let L := logCap n+1
    let D := binaryPoint n
    let b := D.size
    let z := scaledNumerator q (logCap n)
    have aq : PolylogOracle.anchor M k x = q := by simp [q,PolylogOracle.anchor,htest]
    have cert := PolylogOracle.anchor_move_spec M k hk adm x
    have gr := PolylogPrecision.scheduled_central PolylogAdversary.extra hk M adm x J htest
    have h0 : 0 ≤ q := (adm.rationalBounds x).1.trans (cert.2.1.trans_eq aq).le
    have h1 : q ≤ 1 := (aq ▸ cert.2.2.1).le.trans (adm.rationalBounds x).2
    have sw := scaleWork_bound gr h0 h1
    have db := (stored_embed_dictionary hk align depth z).2
    have sb := PolylogEmbed.embedAddr_work D (logCap n) z m.valid m.cache (le_refl b)
    have pos : 1 ≤ L := by dsimp only [L]; omega
    have hb : b ≤ 5+L*3 := PolylogSchedule.capacity_bits (extra := PolylogAdversary.extra) hk le_rfl
    have hbo : b+1 ≤ 9*L := by omega
    have eb : (PolylogEmbed.embedAddr D (logCap n) z m.valid m.cache (le_refl b)).work ≤ 200*L^3 := by
      apply sb.trans
      have h := Nat.pow_le_pow_left hbo 2
      change 1+L*((b+1)^2+10*b+6) ≤ _
      apply (Nat.add_le_add_left (Nat.mul_le_mul_left L (show (b+1)^2+10*b+6 ≤ (9*L)^2+90*L by omega)) _).trans
      nlinarith only [Nat.mul_le_mul_right L pos, Nat.mul_le_mul_right (L^2) pos,
        Nat.one_le_pow 3 L pos]
    have small2 : L^2 ≤ L^4 := Nat.pow_le_pow_right pos (by decide)
    have small3 : L^3 ≤ L^4 := Nat.pow_le_pow_right pos (by decide)
    have small : L ≤ L^4 := Nat.le_self_pow (by decide) _
    change scaleWork q (logCap n) ≤ 54*L^2 at sw
    let audit := (embedTrace m.valid m.cache (le_refl b) (logCap n+1) (D-logCap n) z).run m.heap
    change audit.work ≤ 200000*L^4 at db
    change 4*((PolylogEmbed.embedAddr D (logCap n) z m.valid m.cache (le_refl b)).work+logCap n+4) +
      scaleWork q (logCap n) + audit.work ≤ 60000000*L^4
    have le : logCap n ≤ L := Nat.le_succ _
    omega

end SortingAdversary.Continuous.PolylogWordWriter
