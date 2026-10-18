module

public import SpectreGeometry.PolygonProductKeyNormalRank
public import SpectreGeometry.ComplementaryNormalChart
public import PhysicalRegistration.IsometryTransport

@[expose] public section


/-! Isometric transverse charts onto the two actual independent key normals.
No prescribed coordinate alignment or chart-range premise is needed. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem exists_chart_of_independent_pair (p q : EFour)
    (hind : ∀ a b : ℝ, a • p + b • q = 0 → a = 0 ∧ b = 0) :
    ∃ N : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour, LinearMap.range N.toLinearMap = Submodule.span ℝ {p,q} := by
  have hli : LinearIndependent ℝ ![p,q] := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at hg
    have hz := hind (g 0) (g 1) hg
    fin_cases i <;> simp_all
  have hpair : Set.range ![p,q] = ({p,q} : Set EFour) := by
    ext v
    simp [Matrix.range_cons,or_comm]
  let K := Submodule.span ℝ ({p,q} : Set EFour)
  have hdim : Module.finrank ℝ K = 2 := by
    change Module.finrank ℝ (Submodule.span ℝ ({p,q} : Set EFour)) = 2
    rw [← hpair]
    exact finrank_span_eq_card hli
  let basis : OrthonormalBasis (Fin 2) ℝ K :=
    (stdOrthonormalBasis ℝ K).reindex (finCongr hdim)
  let N : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour := K.subtypeₗᵢ.comp basis.repr.symm.toLinearIsometry
  refine ⟨N,?_⟩
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    exact (basis.repr.symm v).property
  · intro hz
    refine ⟨basis.repr ⟨z,hz⟩,?_⟩
    change (basis.repr.symm (basis.repr ⟨z,hz⟩) : EFour) = z
    simp

theorem pair_mem_chart_range (p q : EFour) (N : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour)
    (hN : LinearMap.range N.toLinearMap = Submodule.span ℝ {p,q}) :
    p ∈ Set.range N ∧ q ∈ Set.range N := by
  change p ∈ LinearMap.range N.toLinearMap ∧ q ∈ LinearMap.range N.toLinearMap
  rw [hN]
  exact ⟨Submodule.subset_span (by simp),Submodule.subset_span (by simp)⟩

theorem exists_product_key_base_normal_chart (u : ProductKeySite) (b : ProductKeySide) :
    ∃ N : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour,
      LinearMap.range N.toLinearMap = Submodule.span ℝ {productKeyOutwardNormal u,productKeySideNormal u b} :=
  exists_chart_of_independent_pair _ _ (product_key_base_normals_combination_eq_zero u b)

theorem exists_product_key_side_normal_chart (u : ProductKeySite) (b c : ProductKeySide)
    (hbc : b.1 ≠ c.1) :
    ∃ N : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour,
      LinearMap.range N.toLinearMap = Submodule.span ℝ {productKeySideNormal u b,productKeySideNormal u c} :=
  exists_chart_of_independent_pair _ _ (product_key_side_normals_combination_eq_zero u b c hbc)

theorem exists_chart_of_placed_independent_pair (p q : EFour)
    (hind : ∀ a b : ℝ, a • p + b • q = 0 → a = 0 ∧ b = 0)
    (f : EFour ≃ᵢ EFour) :
    ∃ N : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour, LinearMap.range N.toLinearMap = Submodule.span ℝ
      {f.toRealAffineIsometryEquiv.linearIsometryEquiv p,
       f.toRealAffineIsometryEquiv.linearIsometryEquiv q} := by
  let L := f.toRealAffineIsometryEquiv.linearIsometryEquiv
  apply exists_chart_of_independent_pair
  intro a b h
  have hpull := congrArg L.symm h
  change L.symm (a • L p + b • L q) = L.symm 0 at hpull
  have hzero : a • p + b • q = 0 := by
    simpa only [map_add,map_smul,L.symm_apply_apply,map_zero] using hpull
  exact hind a b hzero

theorem exists_placed_product_key_base_normal_chart (u : ProductKeySite) (b : ProductKeySide)
    (f : EFour ≃ᵢ EFour) :
    ∃ N : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour, LinearMap.range N.toLinearMap = Submodule.span ℝ
      {f.toRealAffineIsometryEquiv.linearIsometryEquiv (productKeyOutwardNormal u),
       f.toRealAffineIsometryEquiv.linearIsometryEquiv (productKeySideNormal u b)} :=
  exists_chart_of_placed_independent_pair _ _ (product_key_base_normals_combination_eq_zero u b) f

theorem exists_placed_product_key_side_normal_chart (u : ProductKeySite) (b c : ProductKeySide)
    (hbc : b.1 ≠ c.1) (f : EFour ≃ᵢ EFour) :
    ∃ N : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour, LinearMap.range N.toLinearMap = Submodule.span ℝ
      {f.toRealAffineIsometryEquiv.linearIsometryEquiv (productKeySideNormal u b),
       f.toRealAffineIsometryEquiv.linearIsometryEquiv (productKeySideNormal u c)} :=
  exists_chart_of_placed_independent_pair _ _ (product_key_side_normals_combination_eq_zero u b c hbc) f

end
end SpectreGeometry
