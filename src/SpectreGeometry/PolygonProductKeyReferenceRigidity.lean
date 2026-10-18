module

public import SparseMonotiles.PyramidIsometryRigiditySpan
public import SparseMonotiles.PyramidExtremePoints
public import SpectreGeometry.PolygonProductKeyReferenceFinite
public import Mathlib.Tactic.FinCases

@[expose] public section


namespace SpectreGeometry.ProductKeyReference
open SparseMonotiles SparseMonotiles.Contact
noncomputable section

-- Exact optimized recipe, in the common integer scale used by the finite packet.
def referenceBox (j : Fin 2) : BoxKey 4 where
  centre := ![-74143069, -28886910, -10064670, 0]
  radius := ![296572276, 129991095, 75485025, 0]
  apex := ![0, 0, 0, 255255 * (j.val + 1)]
  bump := true

def boxVertices {n : ℕ} (k : BoxKey (n+1)) :
    Option (Fin n → Bool) → Fin (n+1) → ℤ
  | none => k.apex
  | some b => fun j => if hj : j.val < n then
      k.centre j + if b ⟨j.val,hj⟩ then k.radius j else -k.radius j
    else k.centre j

def vertices (j : Fin 2) : Option (Fin 3 → Bool) → Fin 4 → ℤ :=
  boxVertices (referenceBox j)

def vertexIndex : Option (Fin 3 → Bool) → Fin 9
  | none => 0
  | some b => Fin.ofNat 9 (1 + (if b 0 then 1 else 0) +
      (if b 1 then 2 else 0) + (if b 2 then 4 else 0))

set_option maxRecDepth 100000 in
theorem vertices_recipe_binding : ∀ (j : Fin 2) i k,
    vertices j i k = (if j.val = 0 then referenceVertices1 else referenceVertices2) (vertexIndex i) k := by
  decide +kernel

def referenceSolid (j : Fin 2) : Set (Point 4) :=
  keySolid ((referenceBox j).toKeyData referenceDenominator)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem fingerprints_injective : ∀ j : Fin 2,
    Function.Injective (integerDistanceFingerprint (vertices j)) := by
  decide +kernel

theorem scaledIntegerBoxPyramidVertex_eq {n : ℕ} (box : BoxKey (n + 1)) (den : ℤ)
    (hc : box.centre (Fin.last n) = 0) :
    scaledIntegerVertex (boxVertices box) den =
      euclideanPyramidVertex (keyPyramidLo (box.toKeyData den))
        (keyPyramidHi (box.toKeyData den))
        (rationalPoint (box.toKeyData den).apex) := by
  funext j
  cases j with
  | none => rfl
  | some b =>
      ext k
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simp [scaledIntegerVertex, boxVertices, rationalPoint,
          euclideanPyramidVertex, hc]
      · cases hb : b i <;>
          simp [scaledIntegerVertex, boxVertices, rationalPoint,
            euclideanPyramidVertex, keyPyramidLo, keyPyramidHi, BoxKey.toKeyData,
            rationalVertex, i.isLt, hb, add_div, sub_div, neg_div, sub_eq_add_neg]

/-- The finite set and the geometric range agree, with no multiplicity ambiguity. -/
theorem scaledIntegerBoxPyramidVertexFinset_eq_range {n : ℕ}
    (box : BoxKey (n + 1)) (den : ℤ) (hc : box.centre (Fin.last n) = 0) :
    (scaledIntegerVertexFinset (boxVertices box) den : Set (Point (n + 1))) =
      Set.range (euclideanPyramidVertex (keyPyramidLo (box.toKeyData den))
        (keyPyramidHi (box.toKeyData den))
        (rationalPoint (box.toKeyData den).apex)) := by
  classical
  simp only [scaledIntegerVertexFinset, Finset.coe_image, Finset.coe_univ,
    Set.image_univ, scaledIntegerBoxPyramidVertex_eq box den hc]


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

theorem base_interval_pos (j : Fin 2) (i : Fin 3) :
    keyPyramidLo ((referenceBox j).toKeyData referenceDenominator) i <
      keyPyramidHi ((referenceBox j).toKeyData referenceDenominator) i := by
  fin_cases j <;> fin_cases i <;>
    norm_num [keyPyramidLo, keyPyramidHi, referenceBox, referenceDenominator,
      BoxKey.toKeyData, rationalVertex]

theorem height_pos (j : Fin 2) :
    0 < (((referenceBox j).toKeyData referenceDenominator).apex 3 : ℝ) := by
  fin_cases j <;> norm_num [referenceBox, referenceDenominator, BoxKey.toKeyData, rationalVertex]

theorem vertices_affineSpan (j : Fin 2) :
    affineSpan ℝ (scaledIntegerVertexFinset (vertices j) referenceDenominator : Set (Point 4)) = ⊤ := by
  unfold vertices
  rw [scaledIntegerBoxPyramidVertexFinset_eq_range _ _ (by rfl)]
  apply affineSpan_euclideanPyramidVertex
  · intro i
    exact ne_of_lt (base_interval_pos j i)
  · exact ne_of_gt (height_pos j)

theorem reference_extremePoints (j : Fin 2) :
    (referenceSolid j).extremePoints ℝ =
      (scaledIntegerVertexFinset (vertices j) referenceDenominator : Set (Point 4)) := by
  unfold referenceSolid vertices
  rw [scaledIntegerBoxPyramidVertexFinset_eq_range _ _ (by rfl)]
  apply keySolid_extremePoints_eq_euclideanPyramidVertex
  · norm_num [referenceBox, BoxKey.toKeyData, rationalVertex, Fin.last]
  · norm_num [referenceBox, BoxKey.toKeyData, rationalVertex, Fin.last]
  · exact height_pos j
  · intro i
    exact le_of_lt (base_interval_pos j i)

theorem reference_isometry_stabilizer (j : Fin 2) (g : Point 4 ≃ᵢ Point 4)
    (hg : g '' referenceSolid j = referenceSolid j) : g = IsometryEquiv.refl (Point 4) :=
  isometryEquiv_eq_refl_of_integerFingerprint (referenceSolid j) (vertices j)
    (by norm_num [referenceDenominator]) (reference_extremePoints j)
    (vertices_affineSpan j) (fingerprints_injective j) g hg

end
end SpectreGeometry.ProductKeyReference
