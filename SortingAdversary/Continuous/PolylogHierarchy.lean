import SortingAdversary.Continuous.PolylogRouting

/-!
# Sharing children of a hierarchy node

The key of a child consists of two word-sized identifiers: its parent and its
exact dyadic anchor. A pair of persistent binary tables implements this map.
On a hit the stored row is reused. On a miss the new row inherits its parent's
ancestor table, and the next creation index is assigned to it. The list of
full paths in the invariant is used only to specify the meaning of an index.
-/

namespace SortingAdversary.Continuous.PolylogHierarchy

open PolylogRouting Optimal.PrimitiveWork

structure Cursor (h : ℕ) where
  id : ℕ
  row : Row ℕ h

structure Store (h : ℕ) where
  next : ℕ
  children : Table (Table (Option (Cursor h)) h) h

def rootCursor (h : ℕ) : Cursor h := ⟨0, root 0 h⟩

def empty (h : ℕ) : Store h := ⟨1, Table.fill (Table.fill none h) h⟩

def lookup (s : Store h) (p c : ℕ) : Result (Option (Cursor h)) :=
  let d := s.children.get p
  let e := d.value.get c
  ⟨e.value, d.work + e.work + 1⟩

private def install (s : Store h) (p c : ℕ) (v : Cursor h) : Result (Store h) :=
  let d := s.children.get p
  let e := d.value.put c (some v)
  let a := s.children.put p e.value
  ⟨⟨s.next + 1, a.value⟩, d.work + e.work + a.work + 2⟩

def getOrCreate (s : Store h) (p : Cursor h) (c : ℕ) : Result (Cursor h × Store h) :=
  let hit := lookup s p.id c
  match hit.value with
  | some v => ⟨(v, s), hit.work + 1⟩
  | none =>
    let row := child p.row s.next c
    let v := (⟨s.next, row.value⟩ : Cursor h)
    let ins := install s p.id c v
    ⟨(v, ins.value), hit.work + row.work + ins.work + 3⟩

@[simp] theorem lookup_work (s : Store h) (p c : ℕ) : (lookup s p c).work = 8*h+3 := by
  simp [lookup]; omega

private theorem install_work (s : Store h) (p c : ℕ) (v : Cursor h) :
    (install s p c v).work = 14*h+5 := by simp [install]; omega

theorem getOrCreate_work (s : Store h) (p : Cursor h) (c : ℕ) :
    (getOrCreate s p c).work ≤ 27*h+14 := by
  cases hh : (lookup s p.id c).value <;> simp only [getOrCreate, hh, lookup_work, child_work, install_work] <;> omega

theorem adds_at_most_one (s : Store h) (p : Cursor h) (c : ℕ) :
    s.next ≤ (getOrCreate s p c).value.2.next ∧
      (getOrCreate s p c).value.2.next ≤ s.next + 1 := by
  cases hh : (lookup s p.id c).value <;> simp [getOrCreate, hh, install]

private theorem lookup_install (s : Store h) (p c i a : ℕ) (v : Cursor h)
    (hp : p < 2^h) (hc : c < 2^h) (hi : i < 2^h) (ha : a < 2^h) :
    (lookup (install s p c v).value i a).value =
      if i = p ∧ a = c then some v else (lookup s i a).value := by
  simp only [lookup, install, Table.get_put _ _ _ _ hp hi]
  by_cases eq : i = p
  · subst i
    simp [Table.get_put _ _ _ _ hc ha]
  · simp [eq]

def Cursor.At (u : Cursor h) (nodes : List (List ℕ)) (p : List ℕ) : Prop :=
  u.id = nodes.idxOf p ∧ Represents nodes p u.row

theorem Cursor.At.mem {u : Cursor h} {nodes : List (List ℕ)} {p : List ℕ}
    (v : u.At nodes p) : p ∈ nodes := by simpa using v.2.mem p.length le_rfl

theorem Cursor.At.append {u : Cursor h} {nodes : List (List ℕ)} {p : List ℕ}
    (v : u.At nodes p) (more : List (List ℕ)) : u.At (nodes ++ more) p :=
  ⟨by simpa only [List.idxOf_append_of_mem v.mem] using v.1, v.2.append more⟩

structure Valid (s : Store h) (nodes : List (List ℕ)) : Prop where
  count : s.next = nodes.length
  distinct : nodes.Nodup
  sound : ∀ i a, i < 2^h → a < 2^h → ∀ v, (lookup s i a).value = some v →
    ∃ p, p ∈ nodes ∧ nodes.idxOf p = i ∧ v.At nodes (p ++ [a])
  complete : ∀ p a, p ++ [a] ∈ nodes →
    p ∈ nodes ∧ a < 2^h ∧ ∃ v, (lookup s (nodes.idxOf p) a).value = some v

theorem empty_valid (h : ℕ) : Valid (empty h) [[]] := by
  refine ⟨rfl, by simp, ?_, ?_⟩
  · simp [lookup, empty]
  · simp

theorem root_at (h : ℕ) : (rootCursor h).At [[]] [] :=
  ⟨by simp [rootCursor], root_represents ..⟩

private theorem install_valid {s : Store h} {nodes : List (List ℕ)}
    (hs : Valid s nodes) {parent : Cursor h} {p : List ℕ} (hp : parent.At nodes p)
    (c : ℕ) (hc : c < 2^h) (hroom : s.next < 2^h) (hdepth : p.length + 1 < 2^h)
    (miss : (lookup s parent.id c).value = none) :
    let v : Cursor h := ⟨s.next, (child parent.row s.next c).value⟩
    let newNodes := nodes ++ [p ++ [c]]
    Valid (install s parent.id c v).value newNodes ∧ v.At newNodes (p ++ [c]) := by
  dsimp only
  let v : Cursor h := ⟨s.next, (child parent.row s.next c).value⟩
  let q := p ++ [c]
  have fresh : q ∉ nodes := by
    intro hm
    obtain ⟨_, _, z, hz⟩ := hs.complete p c hm
    rw [← hp.1, miss] at hz
    contradiction
  have vp : v.At (nodes ++ [q]) q := by
    constructor
    · change s.next = (nodes ++ [q]).idxOf q
      simp [List.idxOf_append_of_notMem fresh, hs.count]
    · change Represents (nodes ++ [p ++ [c]]) (p ++ [c]) (child parent.row s.next c).value
      rw [hs.count]
      exact child_represents hp.2 c fresh hdepth
  refine ⟨⟨?_, ?_, ?_, ?_⟩, vp⟩
  · simp [install, hs.count]
  · simp [List.nodup_append, hs.distinct]
    rintro a ha rfl
    exact fresh ha
  · intro i a hi ha z hz
    have hpid : parent.id < 2^h := hp.1 ▸ (List.idxOf_lt_length_iff.mpr hp.mem).trans (hs.count ▸ hroom)
    rw [lookup_install _ _ _ _ _ _ hpid hc hi ha] at hz
    split at hz
    · obtain ⟨rfl, rfl⟩ := ‹i = parent.id ∧ a = c›
      cases hz
      exact ⟨p, List.mem_append_left _ hp.mem,
        by rw [List.idxOf_append_of_mem hp.mem, hp.1], vp⟩
    · obtain ⟨b, hb, hid, hv⟩ := hs.sound i a hi ha z hz
      exact ⟨b, List.mem_append_left _ hb, by rwa [List.idxOf_append_of_mem hb], hv.append _⟩
  · intro b a hm
    rcases List.mem_append.mp hm with old | new
    · obtain ⟨hb, ha, z, hz⟩ := hs.complete b a old
      have hpid : parent.id < 2^h := hp.1 ▸ (List.idxOf_lt_length_iff.mpr hp.mem).trans (hs.count ▸ hroom)
      have hi := (List.idxOf_lt_length_iff.mpr hb).trans (hs.count ▸ hroom)
      refine ⟨List.mem_append_left _ hb, ha, ?_⟩
      rw [List.idxOf_append_of_mem hb, lookup_install _ _ _ _ _ _ hpid hc hi ha]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, hz⟩
    · have eq : b ++ [a] = p ++ [c] := List.mem_singleton.mp new
      have both : b = p ∧ a = c := List.concat_inj.mp (by simpa only [List.concat_eq_append] using eq)
      obtain ⟨rfl, rfl⟩ := both
      have hi := (List.idxOf_lt_length_iff.mpr hp.mem).trans (hs.count ▸ hroom)
      refine ⟨List.mem_append_left _ hp.mem, hc, v, ?_⟩
      rw [List.idxOf_append_of_mem hp.mem, hp.1, lookup_install _ _ _ _ _ _ hi hc hi hc, if_pos ⟨rfl,rfl⟩]

/-- Lookups return the unique creation index and ancestor row. All previous
node handles remain valid for the resulting path list by `Cursor.At.append`. -/
theorem getOrCreate_spec {s : Store h} {nodes : List (List ℕ)} (hs : Valid s nodes)
    {parent : Cursor h} {p : List ℕ} (hp : parent.At nodes p) (c : ℕ) (hc : c < 2^h)
    (hroom : s.next < 2^h) (hdepth : p.length + 1 < 2^h) :
    let result := (getOrCreate s parent c).value
    (Valid result.2 nodes ∧ result.1.At nodes (p ++ [c]) ∧ result.2 = s) ∨
    (p ++ [c] ∉ nodes ∧ Valid result.2 (nodes ++ [p ++ [c]]) ∧
      result.1.At (nodes ++ [p ++ [c]]) (p ++ [c]) ∧ result.2.next = s.next + 1) := by
  dsimp only
  cases hh : (lookup s parent.id c).value with
  | none =>
    obtain ⟨hvalid, hv⟩ := install_valid hs hp c hc hroom hdepth hh
    have fresh : p ++ [c] ∉ nodes := by
      intro hm
      obtain ⟨_, _, _, er⟩ := hs.complete _ _ hm
      rw [← hp.1, hh] at er
      contradiction
    apply Or.inr
    simp only [getOrCreate, hh]
    exact ⟨fresh, hvalid, hv, rfl⟩
  | some z =>
    have hi : parent.id < 2^h := hp.1 ▸ (List.idxOf_lt_length_iff.mpr hp.mem).trans (hs.count ▸ hroom)
    obtain ⟨q, hq, he, hz⟩ := hs.sound _ _ hi hc _ hh
    have eq := (List.idxOf_inj hq).mp (he.trans hp.1)
    subst q
    exact Or.inl (by simpa only [getOrCreate, hh] using And.intro hs (And.intro hz (rfl : s = s)))

end SortingAdversary.Continuous.PolylogHierarchy
