module

public import SparseMonotiles.GlobalBodyAffine
public import SparseMonotiles.GenericRidgePoints
public import SparseMonotiles.LocalFiniteness
public import SparseMonotiles.TileTilingGeometry

@[expose] public section

/-!
# Generic ridge points in actual bounded tiling neighborhoods

Local finiteness supplies a finite inventory of physical tiles meeting a fixed
bounded set. Each physical tile receives one arbitrary Euclidean frame before
any ridge point is selected. The fixed global affine fields in those frames
then have a dense set of generic ridge points. In particular, all active fields
of every tile incident to a selected point in the bounded set vanish along the
entire ridge. No registered orientation or lattice is assumed.
-/

namespace SparseMonotiles

open Set Metric

/-- The tiles of a physical tiling meeting a bounded set form a finite subtype.
This is a consequence of the compact body and its positive inball. -/
theorem IsTiling.finite_bounded_meeting_subtype {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))}
    (ht : IsTiling T tiles) (hT : IsCompact T)
    {p : Point d} {r : ℝ} (hr : 0 < r) (hball : ball p r ⊆ T)
    {K : Set (Point d)} (hK : Bornology.IsBounded K) :
    {A : tiles | ((A : Set (Point d)) ∩ K).Nonempty}.Finite := by
  have hf := ht.finite_intersect_of_isBounded hT hr hball hK
  exact (hf.preimage Subtype.val_injective.injOn).subset fun A hA => ⟨A.property, hA⟩

/-- The frames and the entire field inventory are fixed before the dense set is
formed. Only fields belonging to tiles meeting `K` need to be avoided. -/
theorem IsTiling.exists_fixed_frames_bounded_dense_ridge {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))}
    (ht : IsTiling T tiles) (hT : IsCompact T)
    {p : Point d} {r : ℝ} (hr : 0 < r) (hball : ball p r ⊆ T)
    {K : Set (Point d)} (hK : Bornology.IsBounded K)
    {ι : Type*} [Countable ι]
    (fields : (Point d ≃ᵢ Point d) → ι → Point d →ᵃ[ℝ] ℝ)
    (R : AffineSubspace ℝ (Point d)) (hR : (R : Set (Point d)).Nonempty) :
    ∃ g : tiles → Point d ≃ᵢ Point d,
      (∀ A : tiles, (A : Set (Point d)) = g A '' T) ∧
      Dense {x : R | ∀ A : tiles, ((A : Set (Point d)) ∩ K).Nonempty →
        ∀ j, fields (g A) j x = 0 → ∀ y ∈ R, fields (g A) j y = 0} := by
  classical
  choose g hg using fun A : tiles => ht.1 A A.property
  have hf := ht.finite_bounded_meeting_subtype hT hr hball hK
  let I := {A : tiles // ((A : Set (Point d)) ∩ K).Nonempty}
  letI : Fintype I := hf.fintype
  let H : I × ι → AffineSubspace ℝ (Point d) :=
    fun j => affineFormPlane (fields (g j.1.1) j.2) 0
  refine ⟨g, hg, (dense_genericRidgePoints R hR H).mono ?_⟩
  intro x hx A hA j hj y hy
  exact (mem_affineFormPlane _ _ _).mp
    (hx (⟨A, hA⟩, j) ((mem_affineFormPlane _ _ _).mpr hj) hy)

/-- In the fixed chosen frames, all global planes of all bounded-neighborhood
T5 tiles are simultaneously generic. The same fixed fields describe each
whole physical tile by the exact closed Boolean halfspace formula. -/
theorem T5_tiling_fixed_frames_bounded_dense_ridge
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    {K : Set (Point 5)} (hK : Bornology.IsBounded K)
    (R : AffineSubspace ℝ (Point 5)) (hR : (R : Set (Point 5)).Nonempty) :
    ∃ g : tiles → Point 5 ≃ᵢ Point 5,
      (∀ A : tiles, (A : Set (Point 5)) = g A '' T5) ∧
      (∀ A : tiles, (A : Set (Point 5)) =
        closure ((globalBodyFormula keys5 (PyramidHalfspaceIndex 4)).region
          (fun j x => T5GlobalSlacks j ((g A).symm x)))) ∧
      Dense {x : R | ∀ A : tiles, ((A : Set (Point 5)) ∩ K).Nonempty →
        ∀ j, T5WorldAffineFields (g A) j x = 0 →
          ∀ y ∈ R, T5WorldAffineFields (g A) j y = 0} := by
  obtain ⟨g, hg, hd⟩ := ht.exists_fixed_frames_bounded_dense_ridge T5_isCompact
    (by norm_num) T5_centralBall_from_cellCores hK T5WorldAffineFields R hR
  exact ⟨g, hg, fun A => (hg A).trans (T5_copy_global_halfspace_formula (g A)), hd⟩

/-- The corresponding fixed-frame dense generic-ridge theorem for the exact
T7 body, with no registration assumption on any physical copy. -/
theorem T7_tiling_fixed_frames_bounded_dense_ridge
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    {K : Set (Point 7)} (hK : Bornology.IsBounded K)
    (R : AffineSubspace ℝ (Point 7)) (hR : (R : Set (Point 7)).Nonempty) :
    ∃ g : tiles → Point 7 ≃ᵢ Point 7,
      (∀ A : tiles, (A : Set (Point 7)) = g A '' T7) ∧
      (∀ A : tiles, (A : Set (Point 7)) =
        closure ((globalBodyFormula keys7 (PyramidHalfspaceIndex 6)).region
          (fun j x => T7GlobalSlacks j ((g A).symm x)))) ∧
      Dense {x : R | ∀ A : tiles, ((A : Set (Point 7)) ∩ K).Nonempty →
        ∀ j, T7WorldAffineFields (g A) j x = 0 →
          ∀ y ∈ R, T7WorldAffineFields (g A) j y = 0} := by
  obtain ⟨g, hg, hd⟩ := ht.exists_fixed_frames_bounded_dense_ridge T7_isCompact
    (by norm_num) T7_centralBall_from_cellCores hK T7WorldAffineFields R hR
  exact ⟨g, hg, fun A => (hg A).trans (T7_copy_global_halfspace_formula (g A)), hd⟩

/-- A generic family for all tiles meeting `K` controls every tile incident to
any point of `K`; the finite inventory is not chosen after that point. -/
theorem bounded_ridge_generic_controls_incident {d : ℕ}
    {tiles : Set (Set (Point d))} {K : Set (Point d)}
    {ι : Type*} (g : tiles → Point d ≃ᵢ Point d)
    (fields : (Point d ≃ᵢ Point d) → ι → Point d →ᵃ[ℝ] ℝ)
    {R : AffineSubspace ℝ (Point d)} {x : R}
    (hx : ∀ A : tiles, ((A : Set (Point d)) ∩ K).Nonempty →
      ∀ j, fields (g A) j x = 0 → ∀ y ∈ R, fields (g A) j y = 0)
    (hxK : (x : Point d) ∈ K) :
    ∀ A : tiles, (x : Point d) ∈ (A : Set (Point d)) →
      ∀ j, fields (g A) j x = 0 →
        R ≤ affineFormPlane (fields (g A) j) 0 := by
  intro A hxA j hj y hy
  exact (mem_affineFormPlane _ _ _).mpr (hx A ⟨x, hxA, hxK⟩ j hj y hy)

/-- Every nonempty relatively open ridge patch inside a fixed bounded set
contains a point at which every incident T5 tile's active global plane contains
the whole ridge. Frames are selected before the open patch or point. -/
theorem T5_tiling_fixed_frames_generic_point_in_open
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    {K : Set (Point 5)} (hK : Bornology.IsBounded K)
    (R : AffineSubspace ℝ (Point 5)) (hR : (R : Set (Point 5)).Nonempty) :
    ∃ g : tiles → Point 5 ≃ᵢ Point 5,
      (∀ A : tiles, (A : Set (Point 5)) = g A '' T5) ∧
      ∀ O : Set R, IsOpen O → O.Nonempty →
        (∀ x ∈ O, (x : Point 5) ∈ K) →
        ∃ x ∈ O, ∀ A : tiles, (x : Point 5) ∈ (A : Set (Point 5)) →
          ∀ j, T5WorldAffineFields (g A) j x = 0 →
            R ≤ affineFormPlane (T5WorldAffineFields (g A) j) 0 := by
  obtain ⟨g, hg, _, hd⟩ := T5_tiling_fixed_frames_bounded_dense_ridge ht hK R hR
  refine ⟨g, hg, ?_⟩
  intro O hO hne hOK
  obtain ⟨x, hxO, hx⟩ := hd.inter_open_nonempty O hO hne
  exact ⟨x, hxO, bounded_ridge_generic_controls_incident g T5WorldAffineFields hx
    (hOK x hxO)⟩

/-- T7 version of the fixed-frame, incident-plane generic-point conclusion. -/
theorem T7_tiling_fixed_frames_generic_point_in_open
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    {K : Set (Point 7)} (hK : Bornology.IsBounded K)
    (R : AffineSubspace ℝ (Point 7)) (hR : (R : Set (Point 7)).Nonempty) :
    ∃ g : tiles → Point 7 ≃ᵢ Point 7,
      (∀ A : tiles, (A : Set (Point 7)) = g A '' T7) ∧
      ∀ O : Set R, IsOpen O → O.Nonempty →
        (∀ x ∈ O, (x : Point 7) ∈ K) →
        ∃ x ∈ O, ∀ A : tiles, (x : Point 7) ∈ (A : Set (Point 7)) →
          ∀ j, T7WorldAffineFields (g A) j x = 0 →
            R ≤ affineFormPlane (T7WorldAffineFields (g A) j) 0 := by
  obtain ⟨g, hg, _, hd⟩ := T7_tiling_fixed_frames_bounded_dense_ridge ht hK R hR
  refine ⟨g, hg, ?_⟩
  intro O hO hne hOK
  obtain ⟨x, hxO, hx⟩ := hd.inter_open_nonempty O hO hne
  exact ⟨x, hxO, bounded_ridge_generic_controls_incident g T7WorldAffineFields hx
    (hOK x hxO)⟩

#print axioms IsTiling.exists_fixed_frames_bounded_dense_ridge
#print axioms T5_tiling_fixed_frames_bounded_dense_ridge
#print axioms T7_tiling_fixed_frames_bounded_dense_ridge
#print axioms T5_tiling_fixed_frames_generic_point_in_open
#print axioms T7_tiling_fixed_frames_generic_point_in_open

end SparseMonotiles
