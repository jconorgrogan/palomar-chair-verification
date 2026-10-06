module

public import SparseMonotiles.ContactChairChecker
public import SparseMonotiles.KeyCovariance
public import SparseMonotiles.CellCores

@[expose] public section

/-!
A shared occupied integer cell yields a point in the interiors of the actual
physical bodies once their cell-centre/core inclusions are supplied. The witness
is the common unit-cell centre, not an arbitrary carrier point. Registration of
an arbitrary isometry remains a separate obligation.
-/
namespace SparseMonotiles.Contact

noncomputable def cellCentre {d : ℕ} (c : Cell d) : Point d :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm (fun i => (c i : ℝ) + 1/2)

@[simp] theorem cellCentre_apply {d : ℕ} (c : Cell d) (i : Fin d) :
    cellCentre c i = (c i : ℝ) + 1/2 := rfl

theorem cellCentre_mem_integerCellCore {d : ℕ} (mu : ℚ) (hmu : mu < 1/2)
    (c : Cell d) : cellCentre c ∈ integerCellCore mu c := by
  have hm : (mu : ℝ) < 1/2 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hmu
    norm_num at h
    exact h
  intro i
  change (c i : ℝ) + (mu : ℝ) < (c i : ℝ) + 1/2 ∧
    (c i : ℝ) + 1/2 < (c i : ℝ) + 1 - (mu : ℝ)
  constructor <;> linarith

/-- The negative-row lower-cell correction is essential for this identity. -/
@[simp] theorem Pose.euclidean_cellCentre {d : ℕ} (p : Pose d) (c : Cell d) :
    p.euclidean (cellCentre c) = cellCentre (p.cell c) := by
  ext i
  rw [Pose.euclidean_apply]
  simp only [cellCentre_apply]
  cases hn : p.negative i <;> simp [Pose.cell, Pose.sign, hn] <;> ring

theorem exists_binaryCell_of_isChairCell {d : ℕ} {c : Cell d} (hc : IsChairCell c) :
    ∃ bits : Fin d → Bool, (∃ i, bits i = false) ∧ binaryCell bits = c := by
  have h := (mem_chairCells c).mpr hc
  simp only [chairCells, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk] at h
  exact h

/-- Checked whole-core inclusions imply the specific centre inclusions needed by
an overlap certificate. -/
theorem chairCellCentre_mem_interior_of_cores {d : ℕ} {A : Set (Point d)}
    (mu : ℚ) (hmu : mu < 1/2)
    (cores : ∀ bits : Fin d → Bool, (∃ i, bits i = false) →
      carrierCellCore mu bits ⊆ interior A)
    {c : Cell d} (hc : IsChairCell c) : cellCentre c ∈ interior A := by
  rcases exists_binaryCell_of_isChairCell hc with ⟨bits, hbits, rfl⟩
  exact cores bits hbits (cellCentre_mem_integerCellCore mu hmu (binaryCell bits))

/-- The actual common interior point of two registered physical copies. -/
theorem physical_overlap_of_shared_cell {d : ℕ} {A B : Set (Point d)}
    {rootCells sourceCells : Finset (Cell d)}
    (root_centres : ∀ c ∈ rootCells, cellCentre c ∈ interior A)
    (source_centres : ∀ c ∈ sourceCells, cellCentre c ∈ interior B)
    {p : Pose d} {c : Cell d} (hc : c ∈ rootCells)
    (hm : c ∈ sourceCells.image p.cell) :
    cellCentre c ∈ interior A ∩ interior (p.euclidean '' B) := by
  refine ⟨root_centres c hc, ?_⟩
  rcases Finset.mem_image.mp hm with ⟨b, hb, hbc⟩
  have him : p.euclidean (cellCentre b) ∈ interior (p.euclidean '' B) := by
    rw [show (p.euclidean : Point d → Point d) = p.euclidean.toHomeomorph from rfl]
    rw [← p.euclidean.toHomeomorph.image_interior B]
    exact Set.mem_image_of_mem _ (source_centres b hb)
  simpa only [Pose.euclidean_cellCentre, hbc] using him

theorem physical_overlap_of_chair_inverse {d : ℕ} {A : Set (Point d)}
    (centres : ∀ c : Cell d, IsChairCell c → cellCentre c ∈ interior A)
    {p : Pose d} {c : Cell d} (hc : IsChairCell c)
    (hm : IsChairCell (p.inverseCell c)) :
    cellCentre c ∈ interior A ∩ interior (p.euclidean '' A) := by
  apply physical_overlap_of_shared_cell
    (rootCells := chairCells d) (sourceCells := chairCells d)
    (fun x hx => centres x ((mem_chairCells x).mp hx))
    (fun x hx => centres x ((mem_chairCells x).mp hx))
    ((mem_chairCells c).mpr hc)
  exact (mem_image_cell p _ c).mpr ((mem_chairCells _).mpr hm)

/-- A finite overlap certificate refutes physical interior disjointness under
the explicit, separately verified centre inclusion hypothesis. -/
theorem IndexedRejection.overlap_physical_witness {d n : ℕ}
    {g : IndexedGeometry d n} {A : Set (Point d)}
    (centres : ∀ c ∈ g.cells, cellCentre c ∈ interior A)
    {p : Pose d} {c : Cell d} (valid : (IndexedRejection.overlap c).Valid g p) :
    cellCentre c ∈ interior A ∩ interior (p.euclidean '' A) :=
  physical_overlap_of_shared_cell centres centres valid.1 valid.2

theorem carrier_disjoint_of_physical_interiors {d : ℕ} {A B : Set (Point d)}
    {rootCells sourceCells : Finset (Cell d)}
    (root_centres : ∀ c ∈ rootCells, cellCentre c ∈ interior A)
    (source_centres : ∀ c ∈ sourceCells, cellCentre c ∈ interior B)
    {p : Pose d} (h : Disjoint (interior A) (interior (p.euclidean '' B))) :
    Disjoint rootCells (sourceCells.image p.cell) := by
  apply Finset.disjoint_left.mpr
  intro c hc hm
  have hw := physical_overlap_of_shared_cell root_centres source_centres hc hm
  exact Set.disjoint_left.mp h hw.1 hw.2

#print axioms Pose.euclidean_cellCentre
#print axioms IndexedRejection.overlap_physical_witness
#print axioms carrier_disjoint_of_physical_interiors
end SparseMonotiles.Contact
