module

public import LiteralPlanar.SourceCompatibility
public import SpectreGeometry.DeformationHomeomorphism
public import SpectreGeometry.DeformationHomeomorphismGluing

@[expose] public section


/-! Whole-plane pasting for the actual polynomial fan maps. Its only geometric
input is an explicit proper P tiling; compatibility and the contraction bound
are proved from the source geometry. -/
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry FanBounds
open scoped NNReal

variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p)

def globalResidual (x : EPlane) : EPlane :=
  placedTileResidual (p (T.covers x).choose) x

theorem globalResidual_on_tile (i : I) (x : EPlane) (hx : x ∈ p i '' euclideanBody) :
    globalResidual p T x = placedTileResidual (p i) x :=
  placedTileResidual_agrees p T _ i x (T.covers x).choose_spec hx

def placedFan (z : I × Fin 14) : Set EPlane :=
  p z.1 '' (euclideanCoordinates '' triangleBody z.2)

theorem placedFan_subset_body (i : I) (e : Fin 14) :
    placedFan p (i,e) ⊆ p i '' euclideanBody := by
  rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
  exact ⟨euclideanCoordinates z,⟨z,Set.mem_iUnion.mpr ⟨e,hz⟩,rfl⟩,rfl⟩

theorem placedFan_closed (z : I × Fin 14) : IsClosed (placedFan p z) :=
  (((triangleBody_compact z.2).image euclideanCoordinates.continuous).image
    (p z.1).continuous).isClosed

include T in
theorem placedFan_covers (x : EPlane) : ∃ z, x ∈ placedFan p z := by
  obtain ⟨i,y,⟨a,ha,rfl⟩,rfl⟩ := T.covers x
  obtain ⟨e,he⟩ := Set.mem_iUnion.mp ha
  exact ⟨(i,e),euclideanCoordinates a,⟨a,he,rfl⟩,rfl⟩

include T in
theorem placedFan_locallyFinite : LocallyFinite (placedFan p) := by
  intro x
  obtain ⟨U,hU,hfin⟩ := source_locallyFinite p T x
  refine ⟨U,hU,(hfin.prod (Set.finite_univ : (Set.univ : Set (Fin 14)).Finite)).subset ?_⟩
  rintro ⟨i,e⟩ ⟨y,hy,hyU⟩
  exact ⟨⟨y,placedFan_subset_body p i e hy,hyU⟩,Set.mem_univ e⟩

theorem globalResidual_lipschitz : LipschitzWith (90/1024 : ℝ≥0) (globalResidual p T) := by
  apply Deformation.lipschitz_of_locallyFinite_closed_cover (placedFan p)
    (placedFan_locallyFinite p T) (placedFan_closed p) (placedFan_covers p T)
  rintro ⟨i,e⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [globalResidual_on_tile p T i x (placedFan_subset_body p i e hx),
    globalResidual_on_tile p T i y (placedFan_subset_body p i e hy)]
  change dist ((p i).toRealLinearIsometryEquiv _) ((p i).toRealLinearIsometryEquiv _) ≤ _
  rw [(p i).toRealLinearIsometryEquiv.dist_map]
  have hxi : (p i).symm x ∈ euclideanCoordinates '' triangleBody e := by
    obtain ⟨z,hz,rfl⟩ := hx
    simpa only [IsometryEquiv.symm_apply_apply] using hz
  have hyi : (p i).symm y ∈ euclideanCoordinates '' triangleBody e := by
    obtain ⟨z,hz,rfl⟩ := hy
    simpa only [IsometryEquiv.symm_apply_apply] using hz
  have h := (tileResidual_lipschitz_on_fan e).dist_le_mul _ hxi _ hyi
  simpa only [(p i).symm.dist_eq] using h

def curvedHomeomorph : EPlane ≃ₜ EPlane :=
  Deformation.identitySubHomeomorph (fun x => -globalResidual p T x)
    (90/1024) (by norm_num) (globalResidual_lipschitz p T).neg

theorem curvedHomeomorph_apply (x : EPlane) :
    curvedHomeomorph p T x = x + globalResidual p T x := by
  simp only [curvedHomeomorph,Deformation.identitySubHomeomorph_apply,sub_neg_eq_add]

theorem curvedHomeomorph_on_tile (i : I) (x : EPlane) (hx : x ∈ p i '' euclideanBody) :
    curvedHomeomorph p T x = placedTileMap (p i) x := by
  rw [curvedHomeomorph_apply,globalResidual_on_tile p T i x hx,placedTileMap_eq_add]

theorem curvedHomeomorph_image_tile (i : I) :
    curvedHomeomorph p T '' (p i '' euclideanBody) = p i '' curvedBody := by
  apply Set.Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    rw [curvedHomeomorph_on_tile p T i x hx]
    obtain ⟨a,ha,rfl⟩ := hx
    refine ⟨tileMap a,?_,?_⟩
    · rw [←tileMap_image_body]
      exact ⟨a,ha,rfl⟩
    · simp only [placedTileMap,IsometryEquiv.symm_apply_apply]
  · rintro y ⟨x,hx,rfl⟩
    rw [←tileMap_image_body] at hx
    obtain ⟨a,ha,rfl⟩ := hx
    refine ⟨p i a,⟨a,ha,rfl⟩,?_⟩
    rw [curvedHomeomorph_on_tile p T i _ ⟨a,ha,rfl⟩]
    simp only [placedTileMap,IsometryEquiv.symm_apply_apply]

include T

/-- A genuine proper P tiling gives a genuine tiling by the literal quintic
body with exactly the same placements. No target coverage/packing is assumed. -/
theorem source_tiling_to_curved_tiling :
    (∀ x : EPlane, ∃ i, x ∈ p i '' curvedBody) ∧
      Pairwise (fun i j => Disjoint (interior (p i '' curvedBody))
        (interior (p j '' curvedBody))) :=
  Deformation.tiling_transport (curvedHomeomorph p T)
    (fun i => p i '' euclideanBody) (fun i => p i '' curvedBody)
    T.covers T.interiors_disjoint (curvedHomeomorph_image_tile p T)

end
end LiteralPlanar.Forward
