module

public import ProductClosure.IntegralPoseAlgebra
public import ProductClosure.NativeLatticeCells

@[expose] public section

/-! Literal lattice-cell transport by an actual integral signed-permutation
isometry. The lower-corner correction for a negative column is derived from
the coordinate formula, rather than assumed as an abstract lattice action. -/
namespace ProductClosure.NativeCompiler
open Set
noncomputable section
variable {m : ℕ}

/-- The lower corner of the image cell. A negative column takes the interval
`[z, z + 1]` to `[-z - 1, -z]`, before integer translation. -/
def integralCellIndex (p : Equiv.Perm (Fin (m + 1)))
    (b : Fin (m + 1) → Bool) (t z : LatticeIndex m) : LatticeIndex m :=
  fun k => t k + if b (p.symm k) then z (p.symm k) else -z (p.symm k) - 1

@[simp] theorem integralCellIndex_apply (p : Equiv.Perm (Fin (m + 1)))
    (b : Fin (m + 1) → Bool) (t z : LatticeIndex m) (i : Fin (m + 1)) :
    integralCellIndex p b t z (p i) = t (p i) + if b i then z i else -z i - 1 := by
  simp [integralCellIndex]

/-- Exact cell membership transport for the literal predicate witnesses. -/
theorem integral_mem_latticeCell_iff (e : Space m ≃ᵢ Space m)
    (p : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool) (t : LatticeIndex m)
    (hb : ∀ i, placedNormal e (EuclideanSpace.single i 1) =
      sign (b i) • EuclideanSpace.single (p i) 1)
    (ht : e 0 = WithLp.toLp 2 (fun i => (t i : ℝ)))
    (z : LatticeIndex m) (x : Space m) :
    e x ∈ latticeCell (integralCellIndex p b t z) ↔ x ∈ latticeCell z := by
  constructor
  · intro h i
    have hi := h (p i)
    rw [integralCellIndex_apply, integral_signed_permutation_apply e p b t hb ht] at hi
    cases hbi : b i <;> simp [hbi, sign] at hi <;> constructor <;> linarith
  · intro h k
    obtain ⟨i, rfl⟩ := p.surjective k
    have hi := h i
    rw [integralCellIndex_apply, integral_signed_permutation_apply e p b t hb ht]
    cases hbi : b i <;> simp [sign] <;> constructor <;> linarith

/-- Actual set-image equality, including the reflected-cell corner shift. -/
theorem integral_image_latticeCell (e : Space m ≃ᵢ Space m)
    (p : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool) (t : LatticeIndex m)
    (hb : ∀ i, placedNormal e (EuclideanSpace.single i 1) =
      sign (b i) • EuclideanSpace.single (p i) 1)
    (ht : e 0 = WithLp.toLp 2 (fun i => (t i : ℝ))) (z : LatticeIndex m) :
    e '' latticeCell z = latticeCell (integralCellIndex p b t z) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (integral_mem_latticeCell_iff e p b t hb ht z y).mpr hy
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply (integral_mem_latticeCell_iff e p b t hb ht z (e.symm x)).mp
    simpa only [e.apply_symm_apply] using hx

/-- Literal lattice centers are transported to the centers of the image cells. -/
theorem integral_map_latticeCenter (e : Space m ≃ᵢ Space m)
    (p : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool) (t : LatticeIndex m)
    (hb : ∀ i, placedNormal e (EuclideanSpace.single i 1) =
      sign (b i) • EuclideanSpace.single (p i) 1)
    (ht : e 0 = WithLp.toLp 2 (fun i => (t i : ℝ))) (z : LatticeIndex m) :
    e (latticeCenter z) = latticeCenter (integralCellIndex p b t z) := by
  ext k
  obtain ⟨i, rfl⟩ := p.surjective k
  rw [integral_signed_permutation_apply e p b t hb ht]
  change sign (b i) * ((z i : ℝ) + 1 / 2) + (t (p i) : ℝ) =
    (integralCellIndex p b t z (p i) : ℝ) + 1 / 2
  rw [integralCellIndex_apply]
  cases hbi : b i <;> simp [sign] <;> ring

/-- A coordinate neighbor remains a coordinate neighbor in the permuted axis;
a negative column reverses the direction. -/
theorem integralCellIndex_latticeStep (p : Equiv.Perm (Fin (m + 1)))
    (b : Fin (m + 1) → Bool) (t z : LatticeIndex m) (i : Fin (m + 1))
    (positive : Bool) :
    integralCellIndex p b t (latticeStep z i positive) =
      latticeStep (integralCellIndex p b t z) (p i) (b i == positive) := by
  funext k
  obtain ⟨j, rfl⟩ := p.surjective k
  rw [integralCellIndex_apply]
  simp only [latticeStep, Polycube.latticeStep, integralCellIndex_apply, Equiv.apply_eq_iff_eq]
  by_cases hji : j = i
  · subst j
    cases hbi : b i <;> cases positive <;> simp <;> omega
  · simp [hji]

/-- Every output-coordinate neighbor is the image of an explicitly recovered
native-coordinate neighbor. This is the inverse direction of step transport. -/
theorem integralCellIndex_latticeStep_preimage {m : ℕ}
    (p : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool)
    (t z : LatticeIndex m) (k : Fin (m + 1)) (positive : Bool) :
    latticeStep (integralCellIndex p b t z) k positive =
      integralCellIndex p b t
        (latticeStep z (p.symm k) (b (p.symm k) == positive)) := by
  rw [integralCellIndex_latticeStep, p.apply_symm_apply]
  cases hb : b (p.symm k) <;> cases positive <;> rfl

/-- Each actual integral signed-permutation isometry transports all literal
lattice cells and their centers using one common integer lower-corner map. -/
theorem HasIntegralSignedPermutation.lattice_transport {m : ℕ}
    {e : Space m ≃ᵢ Space m} (he : HasIntegralSignedPermutation e) :
    ∃ (p : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool) (t : LatticeIndex m),
      (∀ z, e '' latticeCell z = latticeCell (integralCellIndex p b t z)) ∧
      (∀ z, e (latticeCenter z) = latticeCenter (integralCellIndex p b t z)) ∧
      (∀ z i positive, integralCellIndex p b t (latticeStep z i positive) =
        latticeStep (integralCellIndex p b t z) (p i) (b i == positive)) := by
  obtain ⟨p, b, t, hb, ht⟩ := he
  exact ⟨p, b, t, integral_image_latticeCell e p b t hb ht,
    integral_map_latticeCenter e p b t hb ht, integralCellIndex_latticeStep p b t⟩


#print axioms integral_image_latticeCell
#print axioms integral_map_latticeCenter
#print axioms integralCellIndex_latticeStep
#print axioms integralCellIndex_latticeStep_preimage
#print axioms HasIntegralSignedPermutation.lattice_transport

end
end ProductClosure.NativeCompiler
