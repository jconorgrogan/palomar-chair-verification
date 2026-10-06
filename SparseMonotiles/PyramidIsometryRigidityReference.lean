module

public import SparseMonotiles.PyramidIsometryRigidityBinding
public import SparseMonotiles.PyramidExtremePoints

@[expose] public section

/-!
# Trivial arbitrary-isometry stabilizers of the exact reference keys

These are unconditional theorems about `Canonical.referenceSolid5` and
`Canonical.referenceSolid7`. The extreme-point equality is geometric, the
spanning theorem uses positive widths and nonzero height, and the metric
fingerprint separation is an exact integer certificate. In particular the
isometry is not assumed to permute coordinate axes or preserve a lattice.
-/
namespace SparseMonotiles

/-- The actual key's extreme points are its explicitly indexed Euclidean vertices. -/
theorem keySolid_extremePoints_eq_euclideanPyramidVertex {n : ℕ}
    (k : KeyData (n + 1)) (hc : k.centre (Fin.last n) = 0)
    (hr : k.radius (Fin.last n) = 0) (hh : 0 < keyPyramidHeight k)
    (hw : ∀ i, keyPyramidLo k i ≤ keyPyramidHi k i) :
    (keySolid k).extremePoints ℝ =
      Set.range (euclideanPyramidVertex (keyPyramidLo k) (keyPyramidHi k)
        (rationalPoint k.apex)) := by
  apply (pointPyramidEquiv n).injective.image_injective
  rw [image_extremePoints (pointPyramidEquiv n), pointPyramidEquiv_image_keySolid k hc hr,
    extremePoints_pyramidSolid_eq_range _ _ _ hh hw, ← Set.range_comp]
  apply congrArg Set.range
  funext j
  cases j with
  | none => rfl
  | some b =>
      apply Prod.ext
      · funext i
        simp [Function.comp_def, euclideanPyramidVertex, pyramidVertex,
          pyramidCorner, pointPyramidEquiv_fst]
      · simp [Function.comp_def, euclideanPyramidVertex, pyramidVertex,
          pyramidCorner, pointPyramidEquiv_snd]

namespace Canonical
open Contact

/-- Geometric binding of the complete reference5 extreme-point set. -/
theorem referenceVertices5_extremePoints :
    referenceSolid5.extremePoints ℝ =
      (scaledIntegerVertexFinset referenceVertices5 19200 : Set (Point 5)) := by
  unfold referenceSolid5 referenceVertices5
  rw [scaledIntegerBoxPyramidVertexFinset_eq_range _ _ (by rfl)]
  apply keySolid_extremePoints_eq_euclideanPyramidVertex
  · norm_num [referenceBox5, BoxKey.toKeyData, rationalVertex, Fin.last]
  · norm_num [referenceBox5, BoxKey.toKeyData, rationalVertex, Fin.last]
  · change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
    exact_mod_cast referenceBox5_height_pos true
  · intro i
    unfold keyPyramidLo keyPyramidHi
    exact_mod_cast (le_of_lt (referenceBox5_base_interval_pos true i))

/-- Geometric binding of the complete reference7 extreme-point set. -/
theorem referenceVertices7_extremePoints :
    referenceSolid7.extremePoints ℝ =
      (scaledIntegerVertexFinset referenceVertices7 188160 : Set (Point 7)) := by
  unfold referenceSolid7 referenceVertices7
  rw [scaledIntegerBoxPyramidVertexFinset_eq_range _ _ (by rfl)]
  apply keySolid_extremePoints_eq_euclideanPyramidVertex
  · norm_num [referenceBox7, BoxKey.toKeyData, rationalVertex, Fin.last]
  · norm_num [referenceBox7, BoxKey.toKeyData, rationalVertex, Fin.last]
  · change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
    exact_mod_cast referenceBox7_height_pos true
  · intro i
    unfold keyPyramidLo keyPyramidHi
    exact_mod_cast (le_of_lt (referenceBox7_base_interval_pos true i))

/-- The exact five-dimensional reference key has no nontrivial Euclidean symmetry. -/
theorem referenceSolid5_isometry_stabilizer (g : Point 5 ≃ᵢ Point 5)
    (hg : g '' referenceSolid5 = referenceSolid5) :
    g = IsometryEquiv.refl (Point 5) :=
  isometryEquiv_eq_refl_of_integerFingerprint referenceSolid5 referenceVertices5
    (by norm_num) referenceVertices5_extremePoints referenceVertices5_affineSpan
    referenceVertices5_integerFingerprint_injective g hg

/-- The exact seven-dimensional reference key has no nontrivial Euclidean symmetry. -/
theorem referenceSolid7_isometry_stabilizer (g : Point 7 ≃ᵢ Point 7)
    (hg : g '' referenceSolid7 = referenceSolid7) :
    g = IsometryEquiv.refl (Point 7) :=
  isometryEquiv_eq_refl_of_integerFingerprint referenceSolid7 referenceVertices7
    (by norm_num) referenceVertices7_extremePoints referenceVertices7_affineSpan
    referenceVertices7_integerFingerprint_injective g hg

#print axioms referenceVertices5_extremePoints
#print axioms referenceVertices7_extremePoints
#print axioms referenceSolid5_isometry_stabilizer
#print axioms referenceSolid7_isometry_stabilizer

end Canonical
end SparseMonotiles
