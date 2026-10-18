module

public import SpectreGeometry.FiniteSignCone
public import SpectreGeometry.PolygonProductKeySectorMass
public import SpectreGeometry.PolygonProductKeyFlatGerms
public import SpectreGeometry.PlacedPolygonProductNormals

@[expose] public section


/-! Closed finite-sign cone models for the actual flat, base, and side strata
of an arbitrarily placed optimized product key. Normal-chart containment is
explicit here and is supplied by the separate actual incidence theorem. -/
namespace SpectreGeometry.ProductCrease
noncomputable section
open Set MeasureTheory FiniteConeFan
open scoped InnerProductSpace

/-- Exact body germ with the finite data needed for angular conservation. -/
structure ActualBoundaryConeModel (f : EFour ≃ᵢ EFour) (x : EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) where
  cone : Set EFour
  normals : Finset EFour
  closed : IsClosed cone
  signs : SignDetermined normals cone
  normal_range : ∀ n ∈ normals, n ∈ Set.range L
  germ : LocalConeGerm (f '' polygonProductKeyBody) x cone

def coneAngularMass (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (C : Set EFour) : ℝ := (volume (materialConeDirections L C)).toReal

theorem materialConeDirections_image (f : EFour ≃ᵢ EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (C : Set EFour) :
    materialConeDirections L (f.toRealLinearIsometryEquiv '' C) =
      materialConeDirections (pulledBackNormalChart f L) C := by
  ext θ
  constructor
  · rintro ⟨v,hv,he⟩
    change f.toRealLinearIsometryEquiv.symm (L (PhysicalRegistration.PlanarSectorMeasure.direction θ)) ∈ C
    rw [← he,f.toRealLinearIsometryEquiv.symm_apply_apply]
    exact hv
  · intro h
    exact ⟨f.toRealLinearIsometryEquiv.symm (L (PhysicalRegistration.PlanarSectorMeasure.direction θ)),h,
      f.toRealLinearIsometryEquiv.apply_symm_apply _⟩

/-- Transport only the actual linear displacement action; reflections are allowed. -/
def transportBoundaryConeModel (f : EFour ≃ᵢ EFour) (x : EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (C : Set EFour) (N : Finset EFour)
    (hc : IsClosed C) (hs : SignDetermined N C)
    (hr : ∀ n ∈ N, f.toRealLinearIsometryEquiv n ∈ Set.range L)
    (hg : LocalConeGerm polygonProductKeyBody x C) : ActualBoundaryConeModel f (f x) L where
  cone := f.toRealLinearIsometryEquiv '' C
  normals := N.image f.toRealLinearIsometryEquiv
  closed := f.toRealLinearIsometryEquiv.toHomeomorph.isClosedMap _ hc
  signs := by
    apply (hs.image_linearIsometryEquiv f.toRealLinearIsometryEquiv).mono
    intro n hn
    simpa only [Finset.mem_image] using hn
  normal_range := by
    intro n hn
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    exact hr v hv
  germ := hg.map_isometryEquiv f

private theorem closed_halfspace (n : EFour) : IsClosed {v : EFour | inner ℝ n v ≤ 0} :=
  isClosed_le (continuous_const.inner continuous_id) continuous_const

private theorem signs_union (n m : EFour) :
    SignDetermined {n,m} {v : EFour | inner ℝ n v ≤ 0 ∨ inner ℝ m v ≤ 0} := by
  intro z w h
  exact or_congr (h n (by simp)).1 (h m (by simp)).1

private theorem signs_inter (n m : EFour) :
    SignDetermined {n,m} {v : EFour | inner ℝ n v ≤ 0 ∧ inner ℝ m v ≤ 0} := by
  intro z w h
  exact and_congr (h n (by simp)).1 (h m (by simp)).1

theorem baseMaterialCone_closed_signs (u : ProductKeySite) (b : ProductKeySide) :
    IsClosed (baseMaterialCone u b) ∧
      SignDetermined {productKeyOutwardNormal u, productKeySideNormal u b} (baseMaterialCone u b) := by
  unfold baseMaterialCone
  split_ifs
  · exact ⟨(closed_halfspace _).union (closed_halfspace _),signs_union _ _⟩
  · exact ⟨(closed_halfspace _).inter (closed_halfspace _),signs_inter _ _⟩

theorem sideMaterialCone_closed_signs (u : ProductKeySite) (b c : ProductKeySide) :
    IsClosed (sideMaterialCone u b c) ∧
      SignDetermined {productKeySideNormal u b, productKeySideNormal u c} (sideMaterialCone u b c) := by
  unfold sideMaterialCone
  split_ifs
  · exact ⟨(closed_halfspace _).inter (closed_halfspace _),signs_inter _ _⟩
  · exact ⟨(closed_halfspace _).union (closed_halfspace _),signs_union _ _⟩

/-- Actual flat strata have exactly the half-turn angular mass. -/
theorem exists_flat_boundary_cone_model (f : EFour ≃ᵢ EFour) (x n : EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (hn : n ≠ 0)
    (hr : f.toRealLinearIsometryEquiv n ∈ Set.range L)
    (hg : LocalConeGerm polygonProductKeyBody x {v | inner ℝ n v ≤ 0}) :
    ∃ M : ActualBoundaryConeModel f (f x) L,
      coneAngularMass L M.cone = Real.pi := by
  let M := transportBoundaryConeModel f x L {v | inner ℝ n v ≤ 0} {n}
    (closed_halfspace n) (signDetermined_halfspace n)
    (by intro m hm; simpa using (Finset.mem_singleton.mp hm ▸ hr)) hg
  refine ⟨M,?_⟩
  change (volume (materialConeDirections L (f.toRealLinearIsometryEquiv '' {v | inner ℝ n v ≤ 0}))).toReal = _
  rw [materialConeDirections_image]
  change (volume (sectorHalfplane (pulledBackNormalChart f L) n)).toReal = _
  rw [volume_sectorHalfplane _ hn ((placed_normal_chart_mem_iff f L n).mp hr),
    ENNReal.toReal_ofReal Real.pi_pos.le]

/-- A base ridge supplies a nonflat near-π model and its actual full crease membership. -/
theorem exists_base_boundary_cone_model (f : EFour ≃ᵢ EFour) (x : EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (u : ProductKeySite) (b : ProductKeySide) (hx : x ∈ baseGeneric u b)
    (ho : f.toRealLinearIsometryEquiv (productKeyOutwardNormal u) ∈ Set.range L)
    (hb : f.toRealLinearIsometryEquiv (productKeySideNormal u b) ∈ Set.range L) :
    ∃ M : ActualBoundaryConeModel f (f x) L,
      coneAngularMass L M.cone = baseMaterialAngle u b ∧
      f x ∈ f '' creaseComplex u := by
  have hs := baseMaterialCone_closed_signs u b
  let M := transportBoundaryConeModel f x L (baseMaterialCone u b)
    {productKeyOutwardNormal u, productKeySideNormal u b} hs.1 hs.2
    (by intro n hn; rcases Finset.mem_insert.mp hn with rfl | hn
        · exact ho
        · exact Finset.mem_singleton.mp hn ▸ hb)
    (baseGeneric_local_cone u b x hx)
  refine ⟨M,?_,⟨x,baseCrease_subset_creaseComplex u b hx.1,rfl⟩⟩
  change (volume (materialConeDirections L (f.toRealLinearIsometryEquiv '' baseMaterialCone u b))).toReal = _
  rw [materialConeDirections_image, baseMaterialCone_angular_mass u b _
    ((placed_normal_chart_mem_iff f L _).mp hb) ((placed_normal_chart_mem_iff f L _).mp ho),
    ENNReal.toReal_ofReal]
  linarith [(baseMaterialAngle_bounds u b).1,Real.pi_pos]

theorem exists_side_boundary_cone_model (f : EFour ≃ᵢ EFour) (x : EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (u : ProductKeySite) (b c : ProductKeySide) (hbc : b.1 ≠ c.1)
    (hx : x ∈ sideGeneric u b c)
    (hb : f.toRealLinearIsometryEquiv (productKeySideNormal u b) ∈ Set.range L)
    (hc : f.toRealLinearIsometryEquiv (productKeySideNormal u c) ∈ Set.range L) :
    ∃ M : ActualBoundaryConeModel f (f x) L,
      coneAngularMass L M.cone = sideMaterialAngle u b c ∧
      f x ∈ f '' creaseComplex u := by
  have hs := sideMaterialCone_closed_signs u b c
  let M := transportBoundaryConeModel f x L (sideMaterialCone u b c)
    {productKeySideNormal u b, productKeySideNormal u c} hs.1 hs.2
    (by intro n hn; rcases Finset.mem_insert.mp hn with rfl | hn
        · exact hb
        · exact Finset.mem_singleton.mp hn ▸ hc)
    (sideGeneric_local_cone u b c x hx)
  refine ⟨M,?_,⟨x,sideCrease_subset_creaseComplex u b c hbc hx.1,rfl⟩⟩
  change (volume (materialConeDirections L (f.toRealLinearIsometryEquiv '' sideMaterialCone u b c))).toReal = _
  rw [materialConeDirections_image, sideMaterialCone_angular_mass u b c hbc _
    ((placed_normal_chart_mem_iff f L _).mp hb) ((placed_normal_chart_mem_iff f L _).mp hc),
    ENNReal.toReal_ofReal]
  linarith [(sideMaterialAngle_bounds u b c hbc).1,Real.pi_pos]

end
end SpectreGeometry.ProductCrease
