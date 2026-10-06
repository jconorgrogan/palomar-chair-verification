module

public import SparseMonotiles.PyramidIsometryRigidityMetric
public import SparseMonotiles.CanonicalReferenceKeys

@[expose] public section

/-!
# Exact metric rigidity certificates for the two reference pyramids

The vertex index is `none` for the apex and `some b` for the corner selected by
`b : Fin n → Bool`. The last coordinate of every base vertex is the base
centre's last coordinate. Integer fingerprint checks are ordinary kernel
reduction, not `native_decide`, and are tied to the exact reference BoxKeys.
-/
namespace SparseMonotiles.Canonical

open Contact

/-- All corners and the apex of an integer-encoded coordinate pyramid. -/
def integerBoxPyramidVertex {n : ℕ} (k : BoxKey (n + 1)) :
    Option (Fin n → Bool) → Fin (n + 1) → ℤ
  | none => k.apex
  | some b => fun j => if hj : j.val < n then
      k.centre j + if b ⟨j.val, hj⟩ then k.radius j else -k.radius j
    else k.centre j

/-- Exact integer vertex arrays of the reference keys. -/
def referenceVertices5 : Option (Fin 4 → Bool) → Fin 5 → ℤ :=
  integerBoxPyramidVertex (referenceBox5 true)

def referenceVertices7 : Option (Fin 6 → Bool) → Fin 7 → ℤ :=
  integerBoxPyramidVertex (referenceBox7 true)

/-- The corner-corner contribution is constant; only the apex distance varies. -/
def referenceFingerprint5 : Option (Fin 4 → Bool) → ℤ
  | none => 7713744
  | some b => 14515200 + ∑ k : Fin 5,
      (referenceVertices5 (some b) k - (referenceBox5 true).apex k) ^ 2

def referenceFingerprint7 : Option (Fin 6 → Bool) → ℤ
  | none => 2362305856
  | some b => 4525875200 + ∑ k : Fin 7,
      (referenceVertices7 (some b) k - (referenceBox7 true).apex k) ^ 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Full exact finite metric sum, checked against the vertex coordinates. -/
theorem referenceVertices5_fingerprint :
    integerDistanceFingerprint referenceVertices5 = referenceFingerprint5 := by
  funext i
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Every vertex of the five-dimensional reference has a different intrinsic score. -/
theorem referenceFingerprint5_injective : Function.Injective referenceFingerprint5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Full exact finite metric sum, checked against the vertex coordinates. -/
theorem referenceVertices7_fingerprint :
    integerDistanceFingerprint referenceVertices7 = referenceFingerprint7 := by
  funext i
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Every vertex of the seven-dimensional reference has a different intrinsic score. -/
theorem referenceFingerprint7_injective : Function.Injective referenceFingerprint7 := by
  decide +kernel

theorem referenceVertices5_integerFingerprint_injective :
    Function.Injective (integerDistanceFingerprint referenceVertices5) := by
  rw [referenceVertices5_fingerprint]
  exact referenceFingerprint5_injective

theorem referenceVertices7_integerFingerprint_injective :
    Function.Injective (integerDistanceFingerprint referenceVertices7) := by
  rw [referenceVertices7_fingerprint]
  exact referenceFingerprint7_injective

/-- Exact Euclidean fingerprint separation, without any isometry restriction. -/
theorem referenceVertices5_euclideanFingerprint_injective :
    Set.InjOn (squaredDistanceFingerprint (scaledIntegerVertexFinset referenceVertices5 19200))
      (scaledIntegerVertexFinset referenceVertices5 19200 : Set (Point 5)) :=
  scaledIntegerVertex_fingerprint_injOn _ (by norm_num)
    referenceVertices5_integerFingerprint_injective

theorem referenceVertices7_euclideanFingerprint_injective :
    Set.InjOn (squaredDistanceFingerprint (scaledIntegerVertexFinset referenceVertices7 188160))
      (scaledIntegerVertexFinset referenceVertices7 188160 : Set (Point 7)) :=
  scaledIntegerVertex_fingerprint_injOn _ (by norm_num)
    referenceVertices7_integerFingerprint_injective

#print axioms referenceVertices5_fingerprint
#print axioms referenceFingerprint5_injective
#print axioms referenceVertices7_fingerprint
#print axioms referenceFingerprint7_injective
#print axioms referenceVertices5_euclideanFingerprint_injective
#print axioms referenceVertices7_euclideanFingerprint_injective

end SparseMonotiles.Canonical
