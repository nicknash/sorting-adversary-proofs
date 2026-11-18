import SortingAdversary.Continuous.PolylogAddressOrder
import SortingAdversary.Continuous.PolylogRawBits

/-!
# Fallback from two raw wall addresses

Bisection, comparison, truncation and all writes consume integer handles.
Typing and the agreement with the rational computation appear in proofs.
-/

namespace SortingAdversary.Continuous.PolylogRawAnchor

open PolylogBits PolylogBlockAnchor PolylogAddressOrder
open PolylogRawBits (Output)

variable {S : Store} {H : Heap} {h cap : ℕ}

def probe (table : PolylogRawBits.Table) (H : Heap) {h} (p : Position h)
    (l r : ℕ) : Bool :=
  let t := PolylogRawBits.addUnit table H p l
  !t.2 && !(t.1.heap.lessAddr h r t.1.addr).1

def run (table : PolylogRawBits.Table) (H : Heap) (h D F l r : ℕ) : Output :=
  let search := PolylogAnchor.bisect (fun s => probe table H (placeFor h D (min s F)) l r)
    (Nat.log 2 F+1) 0 F
  let p := placeFor h D (search.1 + 2)
  let t := PolylogRawBits.truncate table H p l
  PolylogRawBits.advance table t.heap p t.addr 3

private theorem run_eq (D F : ℕ) (v : H.Valid) (cache : Cached S H cap) (hc : h ≤ cap)
    {a b : S.Ref h} (l : Cell S H a) (r : Cell S H b) :
    run cache.lookup H h D F l.addr r.addr = PolylogRawBits.erase (fallbackAddr D F v cache hc l r) := by
  have pe (s : ℕ) : probe cache.lookup H (placeFor h D (min s F)) l.addr r.addr =
      fits v cache hc l r (placeFor h D (min s F)) := by
    simp only [probe, fits, PolylogRawBits.addUnit_eq v cache _ hc l]; rfl
  simp only [run, pe]
  let s := (widthSearchAddr D F v cache hc l r).1
  let p := placeFor h D (s+2)
  let t := truncateAddr v cache p hc l
  change PolylogRawBits.advance cache.lookup (PolylogRawBits.truncate cache.lookup H p l.addr).heap p
    (PolylogRawBits.truncate cache.lookup H p l.addr).addr 3 = _
  rw [PolylogRawBits.truncate_eq v cache p hc l]
  change PolylogRawBits.advance (cache.lift t.growth).lookup t.heap p t.cell.addr 3 = _
  rw [PolylogRawBits.advance_eq t.valid (cache.lift t.growth) p hc t.cell]; rfl

structure Written (H : Heap) extends Output where
  valid : heap.Valid
  growth : heap.Extends H
  work : ℕ

/-- Fixed worst-case charge for one fallback. Each address descent also
constructs its bit position with word shifts, comparisons and subtractions.
Bisection has exactly `log₂ F+1` rounds. -/
def workBound (h F : ℕ) : ℕ :=
  (Nat.log 2 F+1)*(24*h+20) + (48*h+24)

/-- The charge dominates the block operations on every possible sequence
of probes, plus six index operations per level for each addressed position. -/
theorem workBound_covers (F : ℕ) (tests : Fin (Nat.log 2 F+1) → Position h)
    (last : Position h) (a b : S.Ref h) :
    let U := uniformSpec S
    (∑ i, ((addUnit S U (tests i) a).work + (PolylogBits.less S h b (addUnit S U (tests i) a).result).2)) +
      (truncate S U last a).2 + (advance S U last (truncate S U last a).1 3).work +
      (Nat.log 2 F+2)*(6*h+8) + 4 ≤ workBound h F := by
  have bound := fallback_block_work F tests last a b
  dsimp only at bound ⊢
  unfold workBound
  nlinarith

/-- Total on natural-number addresses. Two cheap height checks exclude
malformed roots before any mutation. -/
def fallback (D F : ℕ) (v : H.Valid) (ht : H.Typed) (cache : Cached S H cap)
    (hc : h ≤ cap) (left right : ℕ) : Written H :=
  if good : isRoot H h left = true ∧ isRoot H h right = true then
    let out := run cache.lookup H h D F left right
    have ok : out.heap.Valid ∧ out.heap.Extends H := by
      obtain ⟨a,l⟩ := (isRoot_iff S H ht h left).1 good.1
      obtain ⟨b,r⟩ := (isRoot_iff S H ht h right).1 good.2
      let lc : Cell S H a := ⟨left,l⟩
      let rc : Cell S H b := ⟨right,r⟩
      have he : out = _ := run_eq D F v cache hc lc rc
      rw [he]
      exact ⟨(fallbackAddr D F v cache hc lc rc).valid, (fallbackAddr D F v cache hc lc rc).growth⟩
    ⟨out,ok.1,ok.2,workBound h F⟩
  else ⟨⟨H,cache.lookup h false⟩, v, .refl _, 4⟩

theorem fallback_eq (D F : ℕ) (v : H.Valid) (ht : H.Typed) (cache : Cached S H cap)
    (hc : h ≤ cap) {a b : S.Ref h} (l : Cell S H a) (r : Cell S H b) :
    (fallback D F v ht cache hc l.addr r.addr).toOutput =
      PolylogRawBits.erase (fallbackAddr D F v cache hc l r) := by
  have g := And.intro (isRoot_of_rep l.rep) (isRoot_of_rep r.rep)
  simpa only [fallback, dif_pos g] using run_eq D F v cache hc l r

theorem readback (D F : ℕ) (v : H.Valid) (ht : H.Typed) (cache : Cached S H cap)
    (hc : h ≤ cap) (l r : ℕ) (hD : D < 2^h) (hF : F+2 ≤ D)
    (hl : 0 ≤ decode S H D h l) (hr : 0 ≤ decode S H D h r)
    (hw : PolylogAnchor.unit F ≤ decode S H D h r - decode S H D h l)
    (hu : decode S H D h r - decode S H D h l ≤ 1) :
    let w := fallback D F v ht cache hc l r
    decode S w.heap D h w.addr = PolylogAnchor.fallback F (decode S H D h l) (decode S H D h r) := by
  obtain ⟨a,lh⟩ := (nonneg_iff S H D h l).1 hl
  obtain ⟨b,rh⟩ := (nonneg_iff S H D h r).1 hr
  let lc : Cell S H a := ⟨l,lh⟩
  let rc : Cell S H b := ⟨r,rh⟩
  rw [decode_of_rep v lh, decode_of_rep v rh] at hw hu ⊢
  obtain ⟨z, rep, he⟩ := fallbackAddr_represents D F v cache hc lc rc hD hF hw hu
  have g := fallback_eq D F v ht cache hc lc rc
  have g₁ := congrArg Output.heap g
  have g₂ := congrArg Output.addr g
  change decode S (fallback D F v ht cache hc lc.addr rc.addr).heap D h
    (fallback D F v ht cache hc lc.addr rc.addr).addr = _
  rw [show (fallback D F v ht cache hc lc.addr rc.addr).heap = _ from g₁,
    show (fallback D F v ht cache hc lc.addr rc.addr).addr = _ from g₂]
  exact (decode_of_rep (fallbackAddr D F v cache hc lc rc).valid rep).trans he

theorem growth_bound (D F : ℕ) (v : H.Valid) (ht : H.Typed) (cache : Cached S H cap)
    (hc : h ≤ cap) (l r : ℕ) :
    (fallback D F v ht cache hc l r).heap.next ≤ H.next + 7*h := by
  by_cases g : isRoot H h l = true ∧ isRoot H h r = true
  · obtain ⟨a,lh⟩ := (isRoot_iff S H ht h l).1 g.1
    obtain ⟨b,rh⟩ := (isRoot_iff S H ht h r).1 g.2
    let lc : Cell S H a := ⟨l,lh⟩
    let rc : Cell S H b := ⟨r,rh⟩
    have e := congrArg Output.heap (fallback_eq D F v ht cache hc lc rc)
    change (fallback D F v ht cache hc l r).heap = (fallbackAddr D F v cache hc lc rc).heap at e
    rw [e]
    exact fallbackAddr_growth D F v cache hc lc rc
  · simp [fallback, g]

theorem work_bound (D F : ℕ) (v : H.Valid) (ht : H.Typed) (cache : Cached S H cap)
    (hc : h ≤ cap) (l r : ℕ) :
    (fallback D F v ht cache hc l r).work ≤ workBound h F := by
  unfold fallback
  split <;> simp [workBound] <;> omega

end SortingAdversary.Continuous.PolylogRawAnchor
