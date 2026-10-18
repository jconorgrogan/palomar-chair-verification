module

public import PhysicalRegistration.PoseRealization
public import RegisteredPrime.WorldRecognitionBridge
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section

/-! Exact Euclidean realization of an integer-cell registered world by the
literal closed native chair carriers. No keyed-body tiling is assumed. -/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- The row-convention pose transports every literal closed unit cell with
its proved reflected lower-corner correction. -/
theorem poseIsometry_mem_latticeCell_iff {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (z : LatticeIndex m) (x : Space m) :
    poseIsometry q x ∈ latticeCell (q.cell z) ↔ x ∈ latticeCell z := by
  constructor
  · intro h j
    have hi := h (q.frame.inverse j)
    simp only [poseIsometry_apply, RegisteredPrime.Pose.cell,
      RegisteredPrime.RegisteredFrame.linear, q.frame.right_inverse] at hi
    cases hn : q.frame.negative (q.frame.inverse j) <;>
      simp [RegisteredPrime.RegisteredFrame.sign, RegisteredPrime.bit, hn] at hi <;>
      constructor <;> linarith
  · intro h i
    have hi := h (q.frame.perm i)
    simp only [poseIsometry_apply, RegisteredPrime.Pose.cell,
      RegisteredPrime.RegisteredFrame.linear]
    cases hn : q.frame.negative i <;>
      simp [RegisteredPrime.RegisteredFrame.sign, RegisteredPrime.bit, hn] <;>
      constructor <;> linarith

theorem poseIsometry_image_latticeCell {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (z : LatticeIndex m) :
    poseIsometry q '' latticeCell z = latticeCell (q.cell z) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (poseIsometry_mem_latticeCell_iff q z y).mpr hy
  · intro hx
    refine ⟨(poseIsometry q).symm x, ?_, (poseIsometry q).apply_symm_apply x⟩
    apply (poseIsometry_mem_latticeCell_iff q z ((poseIsometry q).symm x)).mp
    simpa only [(poseIsometry q).apply_symm_apply] using hx

/-- Euclidean carrier membership is precisely membership in one of the
literal registered occupied closed unit cells. -/
theorem mem_posed_carrier_iff {m : ℕ} (q : RegisteredPrime.Pose (m+1)) (x : Space m) :
    x ∈ poseIsometry q '' carrier m ↔
      ∃ z : LatticeIndex m, RegisteredPrime.Occupies q z ∧ x ∈ latticeCell z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hy
    refine ⟨q.cell (cellIndex A), (occupies_iff_native_cell q _).mpr ⟨A, rfl⟩, ?_⟩
    exact (poseIsometry_mem_latticeCell_iff q (cellIndex A) y).mpr
      ((latticeCell_cellIndex A).symm ▸ hA)
  · rintro ⟨z, hz, hx⟩
    obtain ⟨A, rfl⟩ := (occupies_iff_native_cell q z).mp hz
    rw [← poseIsometry_image_latticeCell, latticeCell_cellIndex] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨y, Set.mem_iUnion.mpr ⟨A, hy⟩, hxy⟩

/-- All real points, including every lattice boundary point, are covered by
the realized carriers of any registered cell world. -/
theorem registered_carriers_cover {m : ℕ} (W : RegisteredPrime.RegisteredWorld (m+1))
    (x : Space m) : ∃ q, W.tiles q ∧ x ∈ poseIsometry q '' carrier m := by
  obtain ⟨z, hz⟩ := exists_latticeCell x
  obtain ⟨q, hq, hqz⟩ := W.covers z
  exact ⟨q, hq, (mem_posed_carrier_iff q x).mpr ⟨z, hqz, hz⟩⟩

/-- Points avoiding every integer coordinate plane. -/
def RegisteredGridRegular {m : ℕ} (x : Space m) : Prop :=
  ∀ i, x i ∉ Set.range (fun z : ℤ => (z : ℝ))

theorem registeredGridRegular_dense (m : ℕ) :
    Dense {x : Space m | RegisteredGridRegular x} := by
  have hr : Dense (Set.range (fun z : ℤ => (z : ℝ)))ᶜ :=
    (Set.countable_range (fun z : ℤ => (z : ℝ))).dense_compl ℝ
  have hp := dense_pi (Set.univ : Set (Fin (m+1))) (fun _ _ => hr)
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m+1) => ℝ)).toHomeomorph
  have he := hp.preimage e.isOpenMap
  simpa [RegisteredGridRegular, Set.preimage, Set.pi, e] using he

/-- A grid-regular real point belongs to just one closed lattice unit cell. -/
theorem registered_regular_cell_unique {m : ℕ} {x : Space m}
    (hr : RegisteredGridRegular x) {c b : LatticeIndex m}
    (hc : x ∈ latticeCell c) (hb : x ∈ latticeCell b) : c = b := by
  funext i
  have hci := hc i
  have hbi := hb i
  have hnc : x i ≠ (c i : ℝ) := fun h => hr i ⟨c i, h.symm⟩
  have hnb : x i ≠ (b i : ℝ) := fun h => hr i ⟨b i, h.symm⟩
  have hcl : (c i : ℝ) < x i := lt_of_le_of_ne hci.1 hnc.symm
  have hbl : (b i : ℝ) < x i := lt_of_le_of_ne hbi.1 hnb.symm
  have hcb : (c i : ℝ) < ((b i + 1 : ℤ) : ℝ) := by push_cast; linarith [hbi.2]
  have hbc : (b i : ℝ) < ((c i + 1 : ℤ) : ℝ) := by push_cast; linarith [hci.2]
  have hcb' := Int.cast_lt.mp hcb
  have hbc' := Int.cast_lt.mp hbc
  omega

/-- Distinct registered world tiles have disjoint actual carrier interiors.
Density removes all lower-dimensional integer-cell boundary ambiguities. -/
theorem registered_carrier_interiors_disjoint {m : ℕ}
    (W : RegisteredPrime.RegisteredWorld (m+1)) {q r : RegisteredPrime.Pose (m+1)}
    (hq : W.tiles q) (hr : W.tiles r) (hne : q ≠ r) :
    Disjoint (interior (poseIsometry q '' carrier m))
      (interior (poseIsometry r '' carrier m)) := by
  apply Set.disjoint_left.mpr
  intro x hqx hrx
  obtain ⟨y, ⟨hyq, hyr⟩, hreg⟩ := (registeredGridRegular_dense m).inter_open_nonempty
    (interior (poseIsometry q '' carrier m) ∩ interior (poseIsometry r '' carrier m))
    (isOpen_interior.inter isOpen_interior) ⟨x, hqx, hrx⟩
  obtain ⟨c, hqc, hyc⟩ := (mem_posed_carrier_iff q y).mp (interior_subset hyq)
  obtain ⟨b, hrb, hyb⟩ := (mem_posed_carrier_iff r y).mp (interior_subset hyr)
  have hcb := registered_regular_cell_unique hreg hyc hyb
  subst b
  exact hne (W.nonoverlap q r hq hr c hqc hrb).eq

#print axioms registered_carrier_interiors_disjoint
#print axioms poseIsometry_image_latticeCell
#print axioms mem_posed_carrier_iff
#print axioms registered_carriers_cover
end
end PhysicalRegistration.NativeChair
