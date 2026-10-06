module

public import SparseMonotiles.GenericFaceRidges
public import SparseMonotiles.GlobalBodyAffine
public import SparseMonotiles.TileTilingGeometry

@[expose] public section

/-!
# Fixed generic-face families for the exact physical tilings

The bounded-patch tile family is fixed before selecting a generic point. All
carrier refinement equations and key equations are included. The frames are an
arbitrary supplied family, so the result also applies to translation-equivariant
representatives chosen later by the registration proof.
-/
namespace SparseMonotiles

open Set

/-- The complete affine field inventory of every tile meeting a bounded patch
has a relatively dense path-connected generic face subset. -/
theorem T5_tiling_exists_genericFacePoints {tiles : Set (Set (Point 5))}
    (ht : IsTiling T5 tiles) (g : tiles → Point 5 ≃ᵢ Point 5)
    (P : AffineSubspace ℝ (Point 5)) (hP : (P : Set (Point 5)).Nonempty)
    (hcodim : Module.finrank ℝ P.direction + 1 = 5)
    (O : Set (Point 5)) (hOb : Bornology.IsBounded O)
    (hO : IsOpen (Subtype.val ⁻¹' O : Set P)) (hconv : Convex ℝ O)
    (hne : (Subtype.val ⁻¹' O : Set P).Nonempty) :
    ∃ G : Set P, G ⊆ Subtype.val ⁻¹' O ∧ IsPathConnected G ∧
      closure G = closure (Subtype.val ⁻¹' O : Set P) ∧
      ∀ x ∈ G,
        (∀ A : tiles, ((A : Set (Point 5)) ∩ O).Nonempty → ∀ j,
          T5WorldAffineFields (g A) j x = 0 →
          P ≤ affineFormPlane (T5WorldAffineFields (g A) j) 0) ∨
        ∃ R : AffineSubspace ℝ (Point 5), (x : Point 5) ∈ R ∧ R ≤ P ∧
          Module.finrank ℝ R.direction + 2 = 5 ∧
          ∀ A : tiles, ((A : Set (Point 5)) ∩ O).Nonempty → ∀ j,
            T5WorldAffineFields (g A) j x = 0 →
            R ≤ affineFormPlane (T5WorldAffineFields (g A) j) 0 := by
  classical
  let S : Set (Set (Point 5)) := {A | A ∈ tiles ∧ (A ∩ O).Nonempty}
  have hS : S.Finite := T5_tiling_finite_intersect ht hOb
  letI : Fintype S := hS.fintype
  let f : S × GlobalBodyHalfspaceIndex keys5 (PyramidHalfspaceIndex 4) →
      Point 5 →ᵃ[ℝ] ℝ := fun j =>
    T5WorldAffineFields (g ⟨j.1.1,j.1.2.1⟩) j.2
  have hcodim' : Module.finrank ℝ P.direction + 1 = Module.finrank ℝ (Point 5) := by
    simpa only [Point, finrank_euclideanSpace, Fintype.card_fin] using hcodim
  obtain ⟨G,hGO,hpath,hclosure,hG⟩ :=
    exists_genericFacePoints P hP hcodim' f (fun _ => 0) O hO hconv hne
  refine ⟨G,hGO,hpath,hclosure,?_⟩
  intro x hx
  rcases hG x hx with hall | ⟨R,hxR,hRP,hrank,hactive⟩
  · left
    intro A hAO j hj
    exact hall (⟨⟨A,A.property,hAO⟩,j⟩) hj
  · right
    refine ⟨R,hxR,hRP,?_,?_⟩
    · simpa only [Point, finrank_euclideanSpace, Fintype.card_fin] using hrank
    · intro A hAO j hj
      exact hactive (⟨⟨A,A.property,hAO⟩,j⟩) hj

#print axioms T5_tiling_exists_genericFacePoints

/-- The complete affine field inventory of every tile meeting a bounded patch
has a relatively dense path-connected generic face subset. -/
theorem T7_tiling_exists_genericFacePoints {tiles : Set (Set (Point 7))}
    (ht : IsTiling T7 tiles) (g : tiles → Point 7 ≃ᵢ Point 7)
    (P : AffineSubspace ℝ (Point 7)) (hP : (P : Set (Point 7)).Nonempty)
    (hcodim : Module.finrank ℝ P.direction + 1 = 7)
    (O : Set (Point 7)) (hOb : Bornology.IsBounded O)
    (hO : IsOpen (Subtype.val ⁻¹' O : Set P)) (hconv : Convex ℝ O)
    (hne : (Subtype.val ⁻¹' O : Set P).Nonempty) :
    ∃ G : Set P, G ⊆ Subtype.val ⁻¹' O ∧ IsPathConnected G ∧
      closure G = closure (Subtype.val ⁻¹' O : Set P) ∧
      ∀ x ∈ G,
        (∀ A : tiles, ((A : Set (Point 7)) ∩ O).Nonempty → ∀ j,
          T7WorldAffineFields (g A) j x = 0 →
          P ≤ affineFormPlane (T7WorldAffineFields (g A) j) 0) ∨
        ∃ R : AffineSubspace ℝ (Point 7), (x : Point 7) ∈ R ∧ R ≤ P ∧
          Module.finrank ℝ R.direction + 2 = 7 ∧
          ∀ A : tiles, ((A : Set (Point 7)) ∩ O).Nonempty → ∀ j,
            T7WorldAffineFields (g A) j x = 0 →
            R ≤ affineFormPlane (T7WorldAffineFields (g A) j) 0 := by
  classical
  let S : Set (Set (Point 7)) := {A | A ∈ tiles ∧ (A ∩ O).Nonempty}
  have hS : S.Finite := T7_tiling_finite_intersect ht hOb
  letI : Fintype S := hS.fintype
  let f : S × GlobalBodyHalfspaceIndex keys7 (PyramidHalfspaceIndex 6) →
      Point 7 →ᵃ[ℝ] ℝ := fun j =>
    T7WorldAffineFields (g ⟨j.1.1,j.1.2.1⟩) j.2
  have hcodim' : Module.finrank ℝ P.direction + 1 = Module.finrank ℝ (Point 7) := by
    simpa only [Point, finrank_euclideanSpace, Fintype.card_fin] using hcodim
  obtain ⟨G,hGO,hpath,hclosure,hG⟩ :=
    exists_genericFacePoints P hP hcodim' f (fun _ => 0) O hO hconv hne
  refine ⟨G,hGO,hpath,hclosure,?_⟩
  intro x hx
  rcases hG x hx with hall | ⟨R,hxR,hRP,hrank,hactive⟩
  · left
    intro A hAO j hj
    exact hall (⟨⟨A,A.property,hAO⟩,j⟩) hj
  · right
    refine ⟨R,hxR,hRP,?_,?_⟩
    · simpa only [Point, finrank_euclideanSpace, Fintype.card_fin] using hrank
    · intro A hAO j hj
      exact hactive (⟨⟨A,A.property,hAO⟩,j⟩) hj

#print axioms T7_tiling_exists_genericFacePoints

/-- Every surviving point has a common ambient ridge, including when all
active equations contain the whole face. -/
theorem T5_tiling_exists_genericFacePoints_common_ridge
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (P : AffineSubspace ℝ (Point 5)) (hP : (P : Set (Point 5)).Nonempty)
    (hcodim : Module.finrank ℝ P.direction + 1 = 5)
    (O : Set (Point 5)) (hOb : Bornology.IsBounded O)
    (hO : IsOpen (Subtype.val ⁻¹' O : Set P)) (hconv : Convex ℝ O)
    (hne : (Subtype.val ⁻¹' O : Set P).Nonempty) :
    ∃ G : Set P, G ⊆ Subtype.val ⁻¹' O ∧ IsPathConnected G ∧
      closure G = closure (Subtype.val ⁻¹' O : Set P) ∧
      ∀ x ∈ G, ∃ R : AffineSubspace ℝ (Point 5), (x : Point 5) ∈ R ∧ R ≤ P ∧
        Module.finrank ℝ R.direction + 2 = 5 ∧
        ∀ A : tiles, ((A : Set (Point 5)) ∩ O).Nonempty → ∀ j,
          T5WorldAffineFields (g A) j x = 0 →
          R ≤ affineFormPlane (T5WorldAffineFields (g A) j) 0 := by
  obtain ⟨G,hGO,hpath,hclosure,hG⟩ :=
    T5_tiling_exists_genericFacePoints ht g P hP hcodim O hOb hO hconv hne
  refine ⟨G,hGO,hpath,hclosure,?_⟩
  intro x hx
  rcases hG x hx with hall | hridge
  · have hcodim' : Module.finrank ℝ P.direction + 1 = Module.finrank ℝ (Point 5) := by
      simpa only [Point, finrank_euclideanSpace, Fintype.card_fin] using hcodim
    have hdim : 2 ≤ Module.finrank ℝ (Point 5) := by
      simp only [Point, finrank_euclideanSpace, Fintype.card_fin]; omega
    obtain ⟨R,hxR,hRP,hrank⟩ := exists_ridge_through_face_point P hcodim' hdim x
    refine ⟨R,hxR,hRP,?_,?_⟩
    · simpa only [Point, finrank_euclideanSpace, Fintype.card_fin] using hrank
    · intro A hAO j hj
      exact hRP.trans (hall A hAO j hj)
  · exact hridge

#print axioms T5_tiling_exists_genericFacePoints_common_ridge

/-- Every surviving point has a common ambient ridge, including when all
active equations contain the whole face. -/
theorem T7_tiling_exists_genericFacePoints_common_ridge
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (P : AffineSubspace ℝ (Point 7)) (hP : (P : Set (Point 7)).Nonempty)
    (hcodim : Module.finrank ℝ P.direction + 1 = 7)
    (O : Set (Point 7)) (hOb : Bornology.IsBounded O)
    (hO : IsOpen (Subtype.val ⁻¹' O : Set P)) (hconv : Convex ℝ O)
    (hne : (Subtype.val ⁻¹' O : Set P).Nonempty) :
    ∃ G : Set P, G ⊆ Subtype.val ⁻¹' O ∧ IsPathConnected G ∧
      closure G = closure (Subtype.val ⁻¹' O : Set P) ∧
      ∀ x ∈ G, ∃ R : AffineSubspace ℝ (Point 7), (x : Point 7) ∈ R ∧ R ≤ P ∧
        Module.finrank ℝ R.direction + 2 = 7 ∧
        ∀ A : tiles, ((A : Set (Point 7)) ∩ O).Nonempty → ∀ j,
          T7WorldAffineFields (g A) j x = 0 →
          R ≤ affineFormPlane (T7WorldAffineFields (g A) j) 0 := by
  obtain ⟨G,hGO,hpath,hclosure,hG⟩ :=
    T7_tiling_exists_genericFacePoints ht g P hP hcodim O hOb hO hconv hne
  refine ⟨G,hGO,hpath,hclosure,?_⟩
  intro x hx
  rcases hG x hx with hall | hridge
  · have hcodim' : Module.finrank ℝ P.direction + 1 = Module.finrank ℝ (Point 7) := by
      simpa only [Point, finrank_euclideanSpace, Fintype.card_fin] using hcodim
    have hdim : 2 ≤ Module.finrank ℝ (Point 7) := by
      simp only [Point, finrank_euclideanSpace, Fintype.card_fin]; omega
    obtain ⟨R,hxR,hRP,hrank⟩ := exists_ridge_through_face_point P hcodim' hdim x
    refine ⟨R,hxR,hRP,?_,?_⟩
    · simpa only [Point, finrank_euclideanSpace, Fintype.card_fin] using hrank
    · intro A hAO j hj
      exact hRP.trans (hall A hAO j hj)
  · exact hridge

#print axioms T7_tiling_exists_genericFacePoints_common_ridge

end SparseMonotiles
