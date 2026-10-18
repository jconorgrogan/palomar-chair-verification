module

public import ProductClosure.NativePrescribedOrbit
public import ProductClosure.ProductWorldReindex

@[expose] public section

/-! Actual registered carrier contacts supply exposed native facet pairs,
then full free-orbit site pairs. No profile or facet-cover certificate. -/
namespace ProductClosure.NativeCompiler
noncomputable section
open PhysicalRegistration.NativeChair
variable {m : ℕ} {S : Finset (LatticeIndex m)}

/-- Integer adjacency is exactly one signed coordinate step. -/
theorem adjacent_is_latticeStep  (a b : LatticeIndex m)
    (h : RegisteredPrime.Adjacent a b) :
    ∃ j side, b = latticeStep a j side := by
  obtain ⟨j, hj, ht⟩ := h
  rcases hj with hj | hj
  · refine ⟨j, false, ?_⟩
    funext i
    by_cases hij : i = j
    · subst i; simp [latticeStep, Polycube.latticeStep]; omega
    · simp [latticeStep, Polycube.latticeStep, hij, ht i hij]
  · refine ⟨j, true, ?_⟩
    funext i
    by_cases hij : i = j
    · subst i; simp [latticeStep, Polycube.latticeStep]; omega
    · simp [latticeStep, Polycube.latticeStep, hij, ht i hij]

/-- An adjacent cell outside the carrier crosses a literal exposed facet. -/
theorem native_cell_exposed_neighbor  (A : Polycube.Cell S) (b : LatticeIndex m)
    (hab : RegisteredPrime.Adjacent (cellIndex A) b)
    (hb : ¬ ∃ B : Polycube.Cell S, cellIndex B = b) :
    ∃ f : Facet S, facetInsideCell f = A ∧ facetOutsideIndex f = b := by
  obtain ⟨j, side, rfl⟩ := adjacent_is_latticeStep (cellIndex A) b hab
  rcases occupied_cell_neighbor A j side with ⟨B, hB⟩ | ⟨f, hf, hout⟩
  · exact False.elim (hb ⟨B, hB.symm⟩)
  · exact ⟨f, hf, hout.symm⟩

/-- Opposite inside/outside cell transport identifies the actual facet
centers and reverses their actual outward normals. -/
theorem facet_match_of_crossed_cells  (q : RegisteredPrime.Pose (m+1))
    (f g : Facet S)
    (hgo : q.cell (cellIndex (facetInsideCell g)) = facetOutsideIndex f)
    (hgi : q.cell (facetOutsideIndex g) = cellIndex (facetInsideCell f)) :
    poseIsometry q (facetCenter g) = facetCenter f ∧
      placedNormal (poseIsometry q) (outward g) = -outward f := by
  have h₁ := poseIsometry_map_latticeCenter q (cellIndex (facetInsideCell g))
  rw [hgo, latticeCenter_cellIndex, facetInsideCell_center, facetOutsideIndex_center] at h₁
  have h₂ := poseIsometry_map_latticeCenter q (facetOutsideIndex g)
  rw [hgi, latticeCenter_cellIndex, facetInsideCell_center, facetOutsideIndex_center] at h₂
  constructor
  · ext i
    have h₁i := congrArg (fun x : Space m => x i) h₁
    have h₂i := congrArg (fun x : Space m => x i) h₂
    simp only [poseIsometry_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul] at h₁i h₂i ⊢
    linarith
  · ext i
    rw [placedNormal_poseIsometry_apply]
    have h₁i := congrArg (fun x : Space m => x i) h₁
    have h₂i := congrArg (fun x : Space m => x i) h₂
    simp only [poseIsometry_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
      PiLp.neg_apply, smul_eq_mul] at h₁i h₂i ⊢
    linarith

end
end ProductClosure.NativeCompiler
