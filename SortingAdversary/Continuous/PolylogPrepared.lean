import SortingAdversary.Continuous.PolylogPreparedDefs

/-! Agreement of the stored local tests with the rounded oracle. -/

namespace SortingAdversary.Continuous.PolylogPrepared

open PolylogNeighborhood PolylogRows PolylogWallTables PolylogBits FiniteAveraging
open Optimal
open Optimal.PrimitiveWork (Result)
open PolylogOracle (grid cutoff)
open ArbitraryLabels (pathHeight widthThreshold_pos)
open EnclosureParameters (alphabetExponent)
variable {n m h : ℕ}

section Correct

variable {S : Store} {heap : Heap} {level cap : ℕ}

/-- The interpretation of the original wall rows. All fields are proof inputs. -/
structure WallSpec (S : Store) (heap : Heap) (level D : ℕ) (w : Walls ℕ h)
    (A : System (Fin n) ℚ) where
  lower : Fin n → S.Ref level
  upper : Fin n → S.Ref level
  lowerRep : ∀ x, Represents S heap (w.lower.get x.val).value (lower x)
  upperRep : ∀ x, Represents S heap (w.upper.get x.val).value (upper x)
  lowerEq : ∀ x, PolylogPrefix.coordinate S D (lower x) = A.lower x
  upperEq : ∀ x, PolylogPrefix.coordinate S D (upper x) = A.upper x
  bound : ∀ x, value S level (lower x) ≤ 2^D ∧ value S level (upper x) ≤ 2^D

variable {D k : ℕ} {w : Walls ℕ h} {A : System (Fin n) ℚ}
  (valid : heap.Valid) (cache : Cached S heap cap) (hd : level ≤ cap) (hD : D < 2^level)
  (witness : WallSpec S heap level D w A)
  (hk : 0 < k) (roots : List (Fin n))

private abbrev emb := Neighborhood.embedding A k (pathHeight k) hk (halfWidth k) (width_pos k) roots.toFinset
private abbrev localSys := Neighborhood.system A k (pathHeight k) hk (halfWidth k) (width_pos k) roots.toFinset
private abbrev steps := Neighborhood.schedule A k (pathHeight k) hk (halfWidth k) (width_pos k) roots.toFinset
private abbrev index (x : Fin n) (hx : x ∈ roots) :=
  Neighborhood.query A k (pathHeight k) hk (halfWidth k) (width_pos k) roots.toFinset x
    (List.mem_toFinset.mpr hx)

variable (p : Prepared n (Neighborhood.labels A k (pathHeight k) hk (halfWidth k) (width_pos k)
    roots.toFinset).card)
  (he : ∀ i, p.embedding[i] = emb (A := A) hk roots i)
  (hm : ∀ i j, p.data.system.edge i j = (localSys (A := A) hk roots).edge i j)
  (hs : p.schedule = steps (A := A) hk roots)

include he hm in
private theorem represented_system :
    System.mk (fun i => PolylogPrefix.coordinate S D (witness.lower p.embedding[i]))
      (fun i => PolylogPrefix.coordinate S D (witness.upper p.embedding[i]))
      (SparseClosure.lookup p.data.edge) = localSys (A := A) hk roots := by
  have eqsys {ι : Type} (X Y : System ι ℚ) (l : X.lower = Y.lower) (u : X.upper = Y.upper)
      (e : X.edge = Y.edge) : X = Y := by cases X; cases Y; simp_all
  apply eqsys
  · funext i; exact (witness.lowerEq _).trans (congrArg A.lower (he i))
  · funext i; exact (witness.upperEq _).trans (congrArg A.upper (he i))
  · exact funext fun i => funext fun j => hm i j

include valid hd hD witness he hm hs

private theorem pairAt_value (hF : grid k ≤ D) (x y : Fin n) (hx : x ∈ roots) (hy : y ∈ roots) :
    (pairAt w heap (fun j => cache.lookup j false) level D k x y p).value =
      Certificates.selectAnswer k ((PolylogEnclosure.localList A (grid k) k (pathHeight k) hk (cutoff k)
        (widthThreshold_pos ..) roots.toFinset).map (fun I => (I (index (A := A) hk roots x hx),
          I (index (A := A) hk roots y hy)))) := by
  let ix := index (A := A) hk roots x hx
  let iy := index (A := A) hk roots y hy
  simp only [pairAt, pairAtWith, withIndex_eq p _ he x ix (Neighborhood.embedding_query ..),
    withIndex_eq p _ he y iy (Neighborhood.embedding_query ..),withWalls,Params.stage]
  rw [PolylogOracleWork.heapPair_value valid cache hd D _ _ hD hF _ _ _ p.schedule (fun i => witness.lower p.embedding[i]) (fun i => witness.upper p.embedding[i])
    (fun i => by simpa [addresses] using witness.lowerRep p.embedding[i])
    (fun i => by simpa [addresses] using witness.upperRep p.embedding[i])
    (fun i => witness.bound p.embedding[i])]
  exact congrArg₂ (fun sys sched =>
    let lst := PolylogEnclosure.roundedEnclose sys (grid k) (2^alphabetExponent k (pathHeight k)) sched
    Certificates.selectAnswer k (lst.map fun I => (I ix,I iy)))
    (represented_system (cap := cap) witness hk roots p he hm) hs

private theorem thresholdAt_value (x : Fin n) (hx : x ∈ roots) (addr : ℕ) (cut : S.Ref level)
    (hc : Represents S heap addr cut) (hc1 : value S level cut ≤ 2^D)
    (hF : grid k + (steps (A := A) hk roots).length*alphabetExponent k (pathHeight k) ≤ D) :
    (thresholdAt w heap (fun j => cache.lookup j false) level D k x addr p).value =
      Certificates.selectAnswer k ((PolylogEnclosure.localList A (grid k) k (pathHeight k) hk (cutoff k)
        (widthThreshold_pos ..) roots.toFinset).map (fun I => (I (index (A := A) hk roots x hx),
          (PolylogPrefix.coordinate S D cut,PolylogPrefix.coordinate S D cut)))) := by
  let ix := index (A := A) hk roots x hx
  simp only [thresholdAt, thresholdAtWith, withIndex_eq p _ he x ix (Neighborhood.embedding_query ..),withWalls,Params.stage]
  rw [PolylogOracleWork.heapThreshold_value valid cache hd D _ _ hD _ _ _ p.schedule k ix addr (by rwa [hs])
    (fun i => witness.lower p.embedding[i]) (fun i => witness.upper p.embedding[i]) cut (fun i => by simpa [addresses] using witness.lowerRep p.embedding[i])
    (fun i => by simpa [addresses] using witness.upperRep p.embedding[i]) hc
    (fun i => witness.bound p.embedding[i]) hc1]
  exact congrArg₂ (fun sys sched =>
    let lst := PolylogEnclosure.roundedEnclose sys (grid k) (2^alphabetExponent k (pathHeight k)) sched
    Certificates.selectAnswer k (lst.map fun I => (I ix,(PolylogPrefix.coordinate S D cut,PolylogPrefix.coordinate S D cut))))
    (represented_system (cap := cap) witness hk roots p he hm) hs

private theorem centralAt_value (hF : grid k ≤ D) (x : Fin n) (hx : x ∈ roots) :
    (centralAt w heap (fun j => cache.lookup j false) level D k x p).value =
      (Certificates.centralInterval ((PolylogEnclosure.localList A (grid k) k (pathHeight k) hk (cutoff k)
        (widthThreshold_pos ..) roots.toFinset).map (fun I => I (index (A := A) hk roots x hx)))).map
        Certificates.roundUp := by
  let ix := index (A := A) hk roots x hx
  simp only [centralAt, centralAtWith, withIndex_eq p _ he x ix (Neighborhood.embedding_query ..),withWalls,Params.stage]
  rw [PolylogOracleWork.heapCentral_value valid cache hd D _ _ hD hF _ _ _ p.schedule (fun i => witness.lower p.embedding[i]) (fun i => witness.upper p.embedding[i])
    (fun i => by simpa [addresses] using witness.lowerRep p.embedding[i])
    (fun i => by simpa [addresses] using witness.upperRep p.embedding[i])
    (fun i => witness.bound p.embedding[i])]
  exact congrArg₂ (fun sys sched =>
    let lst := PolylogEnclosure.roundedEnclose sys (grid k) (2^alphabetExponent k (pathHeight k)) sched
    (Certificates.centralInterval (lst.map fun I => I ix)).map Certificates.roundUp)
    (represented_system (cap := cap) witness hk roots p he hm) hs

end Correct

section Stored

open Controller
variable {S : Store} {heap : Heap} {level cap D k : ℕ} {w : Walls ℕ h}
   {M : Memory n} {g : Graph n h}
   (valid : heap.Valid) (cache : Cached S heap cap) (hd : level ≤ cap) (hD : D < 2^level)
   (witness : WallSpec S heap level D w M.tree.system) (hk : 0 < k)
   (hg : g.Valid M.tree.system.edge) (hloop : ∀ x, M.tree.system.edge x x = false)

private abbrev env (roots : List (Fin n)) := calibrated (reads g) M.tree.system (adjacent g)
  (adjacent_mem g M.tree.system hg hloop) roots k (pathHeight k) hk (halfWidth k) (width_pos k)

private theorem run_eq (roots : List (Fin n)) (f : ∀ {m}, Prepared n m → Result (Option α)) :
    run g k roots f = ⟨(f (env hk hg hloop roots).value).value,
      (8*h+2*k+10)*(env hk hg hloop roots).work+(f (env hk hg hloop roots).value).work⟩ := by
  simp only [run, runWith, Params.stage, dif_pos hk, if_pos hk]
  exact withPrepared_eq _ M.tree.system _ (adjacent_mem g _ hg hloop) ..

private theorem env_embedding (roots : List (Fin n)) : ∀ i, (env hk hg hloop roots).value.embedding[i] =
    emb (A := M.tree.system) hk roots i :=
  fun _ => calibrated_embedding _ _ (reads_edge g _ hg) ..

private theorem env_edges (roots : List (Fin n)) : ∀ i j,
    (env hk hg hloop roots).value.data.system.edge i j =
      (localSys (A := M.tree.system) hk roots).edge i j :=
  fun _ _ => calibrated_edge _ _ (reads_edge g _ hg) ..

private theorem env_schedule (roots : List (Fin n)) :
    (env hk hg hloop roots).value.schedule = steps (A := M.tree.system) hk roots :=
  calibrated_schedule _ _ (reads_edge g _ hg) ..

include valid hd hD witness hk hg hloop

theorem pair_value (hF : grid k ≤ D) (x y : Fin n) :
    (pair g w heap (fun j => cache.lookup j false) level D k x y).value =
      PolylogOracle.pairTest M k x y := by
  change (run g k _ (pairAt w heap _ level D k x y)).value = _
  rw [run_eq hk hg hloop]
  have t := pairAt_value valid cache hd hD witness hk [x,y] _ (env_embedding hk hg hloop _)
    (env_edges hk hg hloop _) (env_schedule hk hg hloop _) hF x y (by simp) (by simp)
  have transport (Q : Finset (Fin n)) (eq : [x,y].toFinset = Q) (hx : x ∈ Q) (hy : y ∈ Q) :
      (pairAt w heap (fun j => cache.lookup j false) level D k x y (env hk hg hloop [x,y]).value).value = Certificates.selectAnswer k (CertificateSuccess.pairEntries (PolylogEnclosure.localList
        M.tree.system (grid k) k (pathHeight k) hk (cutoff k) (widthThreshold_pos ..) Q)
        (Neighborhood.query _ _ _ hk (halfWidth k) (width_pos k) Q x hx)
        (Neighborhood.query _ _ _ hk (halfWidth k) (width_pos k) Q y hy)) := by
    subst Q; exact t
  simpa only [PolylogOracle.pairTest,dif_pos hk,PolylogSelection.twoIntervals] using
    transport {x,y} (by simp) (by simp) (by simp)

theorem threshold_value (x : Fin n) (addr : ℕ) (cut : S.Ref level) (hc : Represents S heap addr cut)
    (hc1 : value S level cut ≤ 2^D)
    (hF : grid k + (Neighborhood.schedule M.tree.system k (pathHeight k) hk
      (halfWidth k) (width_pos k) {x}).length*alphabetExponent k (pathHeight k) ≤ D) :
    (threshold g w heap (fun j => cache.lookup j false) level D k x addr).value =
      PolylogOracle.thresholdTest M k x (PolylogPrefix.coordinate S D cut) := by
  change (run g k _ (thresholdAt w heap _ level D k x addr)).value = _
  rw [run_eq hk hg hloop]
  have t := thresholdAt_value valid cache hd hD witness hk [x] _ (env_embedding hk hg hloop _)
    (env_edges hk hg hloop _) (env_schedule hk hg hloop _) x (by simp) addr cut hc hc1
    (by unfold steps; rw [show [x].toFinset = {x} by simp]; exact hF)
  have transport (Q : Finset (Fin n)) (eq : [x].toFinset = Q) (hx : x ∈ Q) :
      (thresholdAt w heap (fun j => cache.lookup j false) level D k x addr (env hk hg hloop [x]).value).value = Certificates.selectAnswer k (CertificateSuccess.thresholdEntries (PolylogEnclosure.localList
        M.tree.system (grid k) k (pathHeight k) hk (cutoff k) (widthThreshold_pos ..) Q)
        (Neighborhood.query _ _ _ hk (halfWidth k) (width_pos k) Q x hx) (PolylogPrefix.coordinate S D cut)) := by
    subst Q; exact t
  simpa only [PolylogOracle.thresholdTest,dif_pos hk,PolylogSelection.thresholdIntervals] using
    transport {x} (by simp) (by simp)

theorem central_value (hF : grid k ≤ D) (x : Fin n) :
    (central g w heap (fun j => cache.lookup j false) level D k x).value =
      (PolylogOracle.centralTest M k x).map Certificates.roundUp := by
  change (run g k _ (centralAt w heap _ level D k x)).value = _
  rw [run_eq hk hg hloop]
  have t := centralAt_value valid cache hd hD witness hk [x] _ (env_embedding hk hg hloop _)
    (env_edges hk hg hloop _) (env_schedule hk hg hloop _) hF x (by simp)
  have transport (Q : Finset (Fin n)) (eq : [x].toFinset = Q) (hx : x ∈ Q) :
      (centralAt w heap (fun j => cache.lookup j false) level D k x (env hk hg hloop [x]).value).value = (Certificates.centralInterval ((PolylogEnclosure.localList M.tree.system (grid k)
        k (pathHeight k) hk (cutoff k) (widthThreshold_pos ..) Q).map
        (fun I => I (Neighborhood.query _ _ _ hk (halfWidth k) (width_pos k) Q x hx)))).map Certificates.roundUp := by
    subst Q; exact t
  simpa only [PolylogOracle.centralTest,dif_pos hk,PolylogSelection.oneIntervals] using
    transport {x} (by simp) (by simp)

end Stored

end SortingAdversary.Continuous.PolylogPrepared
