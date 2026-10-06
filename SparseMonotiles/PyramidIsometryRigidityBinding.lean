module

public import SparseMonotiles.PyramidIsometryRigidityCertificates
public import SparseMonotiles.PyramidIsometryRigiditySpan
public import SparseMonotiles.ReferenceKeyHalfspaces

@[expose] public section

/-! # Binding the intrinsic integer metric certificates to the actual reference pyramids -/
namespace SparseMonotiles.Canonical

open Contact

/-- The numeric certificate's vertices are precisely the Euclidean base corners and apex. -/
theorem scaledIntegerBoxPyramidVertex_eq {n : ℕ} (box : BoxKey (n + 1)) (den : ℤ)
    (hc : box.centre (Fin.last n) = 0) :
    scaledIntegerVertex (integerBoxPyramidVertex box) den =
      euclideanPyramidVertex (keyPyramidLo (box.toKeyData den))
        (keyPyramidHi (box.toKeyData den))
        (rationalPoint (box.toKeyData den).apex) := by
  funext j
  cases j with
  | none => rfl
  | some b =>
      ext k
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simp [scaledIntegerVertex, integerBoxPyramidVertex, rationalPoint,
          euclideanPyramidVertex, hc]
      · cases hb : b i <;>
          simp [scaledIntegerVertex, integerBoxPyramidVertex, rationalPoint,
            euclideanPyramidVertex, keyPyramidLo, keyPyramidHi, BoxKey.toKeyData,
            rationalVertex, i.isLt, hb, add_div, sub_div, neg_div, sub_eq_add_neg]

/-- The finite set and the geometric range agree, with no multiplicity ambiguity. -/
theorem scaledIntegerBoxPyramidVertexFinset_eq_range {n : ℕ}
    (box : BoxKey (n + 1)) (den : ℤ) (hc : box.centre (Fin.last n) = 0) :
    (scaledIntegerVertexFinset (integerBoxPyramidVertex box) den : Set (Point (n + 1))) =
      Set.range (euclideanPyramidVertex (keyPyramidLo (box.toKeyData den))
        (keyPyramidHi (box.toKeyData den))
        (rationalPoint (box.toKeyData den).apex)) := by
  classical
  simp only [scaledIntegerVertexFinset, Finset.coe_image, Finset.coe_univ,
    Set.image_univ, scaledIntegerBoxPyramidVertex_eq box den hc]

/-- The reference5 metric-certificate vertices are a full affine spanning set. -/
theorem referenceVertices5_affineSpan :
    affineSpan ℝ (scaledIntegerVertexFinset referenceVertices5 19200 : Set (Point 5)) = ⊤ := by
  unfold referenceVertices5
  rw [scaledIntegerBoxPyramidVertexFinset_eq_range _ _ (by rfl)]
  apply affineSpan_euclideanPyramidVertex
  · intro i
    apply ne_of_lt
    have hi := referenceBox5_base_interval_pos true i
    unfold keyPyramidLo keyPyramidHi
    exact_mod_cast hi
  · change (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ) ≠ 0
    exact_mod_cast (ne_of_gt (referenceBox5_height_pos true))

/-- The reference7 metric-certificate vertices are a full affine spanning set. -/
theorem referenceVertices7_affineSpan :
    affineSpan ℝ (scaledIntegerVertexFinset referenceVertices7 188160 : Set (Point 7)) = ⊤ := by
  unfold referenceVertices7
  rw [scaledIntegerBoxPyramidVertexFinset_eq_range _ _ (by rfl)]
  apply affineSpan_euclideanPyramidVertex
  · intro i
    apply ne_of_lt
    have hi := referenceBox7_base_interval_pos true i
    unfold keyPyramidLo keyPyramidHi
    exact_mod_cast hi
  · change (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ) ≠ 0
    exact_mod_cast (ne_of_gt (referenceBox7_height_pos true))

#print axioms scaledIntegerBoxPyramidVertexFinset_eq_range
#print axioms referenceVertices5_affineSpan
#print axioms referenceVertices7_affineSpan

end SparseMonotiles.Canonical
