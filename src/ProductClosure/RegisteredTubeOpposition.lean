module

public import ProductClosure.RegisteredTubeSeparation
public import ProductClosure.NativePrescribedOrbit
public import ProductClosure.ProductWorldReindex

@[expose] public section

/-! Genuine occupied-cell separation forces opposite normals at tube intersections. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration.NativeChair
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

theorem registered_aligned_normals_eq_or_neg
    (q : RegisteredPrime.Pose (m+1)) (f g : Facet S)
    (haxis : q.frame.perm (normalIndex f) = normalIndex g) :
    placedNormal (poseIsometry q) (outward g) = outward f ∨
      placedNormal (poseIsometry q) (outward g) = -outward f := by
  let s : ℝ := (q.frame.sign (normalIndex f) : ℝ) * normalSign g
  have hf : placedNormal (poseIsometry q) (outward g) =
      s • EuclideanSpace.single (normalIndex f) 1 := by
    ext i
    rw [placedNormal_poseIsometry_apply]
    by_cases hi : i = normalIndex f
    · subst i
      simp [outward, haxis, s]
    · have hp : q.frame.perm i ≠ normalIndex g := by
        intro he
        have h := (rowPermutation q.frame).injective (he.trans haxis.symm)
        exact hi h
      simp [outward, hi, hp]
  have habs : |s| = |normalSign f| := by
    rw [abs_normalSign]
    dsimp [s]
    rw [abs_mul, abs_normalSign, mul_one]
    cases hn : q.frame.negative (normalIndex f) <;>
      norm_num [RegisteredPrime.RegisteredFrame.sign, hn]
  rcases abs_eq_abs.mp habs with hs | hs
  · left; rw [hf, hs]; rfl
  · right; rw [hf, hs, neg_smul]; rfl

/-- Equal normals and facet centers force the same occupied cell center. -/
theorem registered_facet_same_normal_not_disjoint
    (q : RegisteredPrime.Pose (m+1)) (f g : Facet S)
    (hc : poseIsometry q (facetCenter g) = facetCenter f)
    (hn : placedNormal (poseIsometry q) (outward g) = outward f) :
    ¬ Disjoint (S : Set (LatticeIndex m)) (World.placedCells S q) := by
  have hcenter : poseIsometry q (cellCenter (facetInsideCell g)) =
      cellCenter (facetInsideCell f) := by
    rw [facetInsideCell_center, facetInsideCell_center]
    rw [sub_eq_add_neg, ← neg_smul, isometry_map_add_smul, hc, hn]
    module
  have hcell : q.cell (cellIndex (facetInsideCell g)) = cellIndex (facetInsideCell f) := by
    apply latticeCenter_injective
    rw [← poseIsometry_map_latticeCenter q, latticeCenter_cellIndex,
      latticeCenter_cellIndex, hcenter]
  intro hd
  apply Set.disjoint_left.mp hd f.cell.property
  refine ⟨g.cell.val, g.cell.property, ?_⟩
  simpa only [World.poseCellIndex_eq_cell, cellIndex, facetInsideCell] using hcell

/-- Opposite normals follow from actual tube intersection and cell nonoverlap. -/
theorem registered_closedTube_intersection_opposed {J : ℕ} (hm : 2 ≤ m)
    (q : RegisteredPrime.Pose (m+1)) (u v : Site S)
    (hx : (closedTube J u ∩ poseIsometry q '' closedTube J v).Nonempty)
    (hd : Disjoint (S : Set (LatticeIndex m)) (World.placedCells S q)) :
    placedNormal (poseIsometry q) (outward v.1) = -outward u.1 := by
  have hdata := registered_closedTube_intersection_facet_data hm q u v hx
  have haxis : q.frame.perm (normalIndex u.1) = normalIndex v.1 := by
    rw [hdata.1, registeredFacetAxis_perm]
  rcases registered_aligned_normals_eq_or_neg q u.1 v.1 haxis with he | ho
  · exact False.elim (registered_facet_same_normal_not_disjoint q u.1 v.1
      (registered_closedTube_intersection_facetCenter hm q u v hx) he hd)
  · exact ho

#print axioms registered_closedTube_intersection_opposed
end
end ProductClosure.NativeCompiler
