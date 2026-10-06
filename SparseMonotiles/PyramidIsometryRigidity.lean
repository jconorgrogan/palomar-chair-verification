module

public import SparseMonotiles.Model
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

@[expose] public section

/-!
# Rigidity under arbitrary Euclidean isometries

This module deliberately starts from `IsometryEquiv`, not a signed coordinate
permutation. Finite extreme-point metric fingerprints can certify a trivial
stabilizer without presupposing any alignment of the box edges. The fingerprint
of a vertex is the sum of its squared distances to all vertices.
-/
namespace SparseMonotiles

/-- An intrinsic, isometry-invariant fingerprint of a finite metric set. -/
noncomputable def squaredDistanceFingerprint {X : Type*} [MetricSpace X]
    (s : Finset X) (x : X) : ℝ := ∑ y ∈ s, dist x y ^ 2

/-- Setwise invariance of a finite set preserves its distance fingerprint. -/
theorem squaredDistanceFingerprint_isometry {X : Type*} [MetricSpace X]
    (s : Finset X) (g : X ≃ᵢ X) (hg : g '' (s : Set X) = s) (x : X) :
    squaredDistanceFingerprint s (g x) = squaredDistanceFingerprint s x := by
  classical
  have hmaps : ∀ y ∈ s, g y ∈ s := by
    intro y hy
    have : g y ∈ g '' (s : Set X) := ⟨y, hy, rfl⟩
    rwa [hg] at this
  have hsurj : (s : Set X).SurjOn g (s : Set X) := by
    intro y hy
    have : y ∈ g '' (s : Set X) := by rwa [hg]
    exact this
  symm
  unfold squaredDistanceFingerprint
  exact Finset.sum_nbij g hmaps g.injective.injOn hsurj
    (fun y _ => by rw [g.dist_eq])

/-- Distinct intrinsic fingerprints force every point to be fixed individually. -/
theorem isometry_fixes_finset_of_fingerprint_injective {X : Type*} [MetricSpace X]
    (s : Finset X) (hf : Set.InjOn (squaredDistanceFingerprint s) (s : Set X))
    (g : X ≃ᵢ X) (hg : g '' (s : Set X) = s) :
    ∀ x ∈ s, g x = x := by
  intro x hx
  have hgx : g x ∈ (s : Set X) := by
    rw [← hg]
    exact ⟨x, hx, rfl⟩
  exact hf hgx hx (squaredDistanceFingerprint_isometry s g hg x)

/-- Affine equivalences transport extreme points, including translations. -/
theorem affineEquiv_image_extremePoints {d : ℕ}
    (g : Point d ≃ᵃ[ℝ] Point d) (s : Set (Point d)) :
    g '' s.extremePoints ℝ = (g '' s).extremePoints ℝ := by
  have hforward (f : Point d ≃ᵃ[ℝ] Point d) (A : Set (Point d)) :
      f '' A.extremePoints ℝ ⊆ (f '' A).extremePoints ℝ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    intro y hy z hz hseg
    rcases hy with ⟨y, hy, rfl⟩
    rcases hz with ⟨z, hz, rfl⟩
    have hxy : x ∈ openSegment ℝ y z := by
      apply f.injective.mem_set_image.mp
      rw [show (f : Point d → Point d) = f.toAffineMap from rfl,
        image_openSegment]
      exact hseg
    exact congrArg f (hx.2 hy hz hxy)
  apply Set.Subset.antisymm (hforward g s)
  intro y hy
  have hback : g.symm y ∈ (g.symm '' (g '' s)).extremePoints ℝ :=
    hforward g.symm (g '' s) ⟨y, hy, rfl⟩
  have hid : g.symm '' (g '' s) = s := by
    ext x
    simp
  rw [hid] at hback
  exact ⟨g.symm y, hback, g.apply_symm_apply y⟩

/-- Mazur-Ulam makes preservation of extreme points valid for an arbitrary
Euclidean isometry, with no initial orthogonal-matrix or lattice hypothesis. -/
theorem isometryEquiv_image_extremePoints {d : ℕ}
    (g : Point d ≃ᵢ Point d) (s : Set (Point d)) :
    g '' s.extremePoints ℝ = (g '' s).extremePoints ℝ :=
  affineEquiv_image_extremePoints g.toRealAffineIsometryEquiv.toAffineEquiv s

/-- An arbitrary Euclidean isometry fixing an affinely spanning set is identity. -/
theorem isometryEquiv_eq_refl_of_affineSpan_eq_top {d : ℕ}
    (g : Point d ≃ᵢ Point d) (s : Set (Point d))
    (hspan : affineSpan ℝ s = ⊤) (hfix : ∀ x ∈ s, g x = x) :
    g = IsometryEquiv.refl (Point d) := by
  apply IsometryEquiv.ext
  intro x
  have hx : x ∈ affineSpan ℝ s := by rw [hspan]; trivial
  let f := g.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap
  change f x = x
  refine affineSpan_induction hx hfix ?_
  intro c u v w hu hv hw
  rw [f.map_vadd, f.linear.map_smul, f.linearMap_vsub, hu, hv, hw]

/-- A reusable certificate for full arbitrary-isometry rigidity of a polytope.
All geometric obligations (the exact extreme-point set and spanning) and all
metric separation obligations are explicit hypotheses. -/
theorem isometryEquiv_eq_refl_of_extremePoints_fingerprint {d : ℕ}
    (K : Set (Point d)) (v : Finset (Point d))
    (hext : K.extremePoints ℝ = (v : Set (Point d)))
    (hspan : affineSpan ℝ (v : Set (Point d)) = ⊤)
    (hf : Set.InjOn (squaredDistanceFingerprint v) (v : Set (Point d)))
    (g : Point d ≃ᵢ Point d) (hg : g '' K = K) :
    g = IsometryEquiv.refl (Point d) := by
  have hv : g '' (v : Set (Point d)) = v := by
    rw [← hext, isometryEquiv_image_extremePoints, hg]
  exact isometryEquiv_eq_refl_of_affineSpan_eq_top g v hspan
    (isometry_fixes_finset_of_fingerprint_injective v hf g hv)

#print axioms squaredDistanceFingerprint_isometry
#print axioms isometry_fixes_finset_of_fingerprint_injective
#print axioms isometryEquiv_image_extremePoints
#print axioms isometryEquiv_eq_refl_of_extremePoints_fingerprint

end SparseMonotiles
