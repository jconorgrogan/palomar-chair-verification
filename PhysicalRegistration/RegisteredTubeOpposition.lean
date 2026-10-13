module

public import PhysicalRegistration.RegisteredTubeSeparation
public import PrimeFacetClosure.NativeFacetGeometry

@[expose] public section

/-! Intersecting registered tubes of carrier-disjoint tiles have opposite
actual outward normals. Normal opposition is derived, not a matching premise. -/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- For aligned coordinate-normal axes the actual unit normals are equal or
opposite; this includes every signed registered permutation. -/
theorem registered_aligned_normals_eq_or_neg {m : ℕ}
    (q : RegisteredPrime.Pose (m+1)) (f g : Facet m)
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
  · left
    rw [hf, hs]
    rfl
  · right
    rw [hf, hs, neg_smul]
    rfl

/-- Equal normal directions and a common facet center force exactly the
same occupied inside cell, contradicting registered carrier disjointness. -/
theorem registered_facet_same_normal_not_disjoint {m : ℕ}
    (q : RegisteredPrime.Pose (m+1)) (f g : Facet m)
    (hc : poseIsometry q (facetCenter g) = facetCenter f)
    (hn : placedNormal (poseIsometry q) (outward g) = outward f) :
    ¬ RegisteredPrime.Disjoint (RegisteredPrime.identityPose (m+1)) q := by
  have hcenter : poseIsometry q (cellCenter (facetInsideCell g)) =
      cellCenter (facetInsideCell f) := by
    rw [facetInsideCell_center, facetInsideCell_center]
    rw [sub_eq_add_neg, ← neg_smul, isometry_map_add_smul, hc, hn]
    module
  have hcell : q.cell (cellIndex (facetInsideCell g)) = cellIndex (facetInsideCell f) := by
    apply latticeCenter_injective
    rw [← (poseIsometry_realizes q).map_latticeCenter, latticeCenter_cellIndex,
      latticeCenter_cellIndex, hcenter]
  intro hd
  apply hd (cellIndex (facetInsideCell f))
  constructor
  · apply (occupies_iff_native_cell (RegisteredPrime.identityPose (m+1)) _).mpr
    exact ⟨facetInsideCell f, RegisteredPrime.identity_cell _⟩
  · exact (occupies_iff_native_cell q _).mpr ⟨facetInsideCell g, hcell⟩

/-- The opposite-normal premise required by exact tube matching is a
consequence of real tube intersection and genuine occupied-cell disjointness. -/
theorem registered_closedTube_intersection_opposed {m J : ℕ} (hm : 2 ≤ m)
    (q : RegisteredPrime.Pose (m+1)) (u v : Site m)
    (hx : (closedTube J u ∩ poseIsometry q '' closedTube J v).Nonempty)
    (hd : RegisteredPrime.Disjoint (RegisteredPrime.identityPose (m+1)) q) :
    placedNormal (poseIsometry q) (outward v.1) = -outward u.1 := by
  have hdata := registered_closedTube_intersection_facet_data hm q u v hx
  have haxis : q.frame.perm (normalIndex u.1) = normalIndex v.1 := by
    rw [hdata.1, registeredFacetAxis_perm]
  rcases registered_aligned_normals_eq_or_neg q u.1 v.1 haxis with he | ho
  · exact False.elim (registered_facet_same_normal_not_disjoint q u.1 v.1
      (registered_closedTube_intersection_facetCenter hm q u v hx) he hd)
  · exact ho

end
end PhysicalRegistration.NativeChair
