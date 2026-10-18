module

public import SpectreGeometry.ReverseClusterTriangulationHexReal
public import SpectreGeometry.ReverseSourceHexCover

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate

theorem baseHexBody_mem_iff (x : RealPoint) : x ∈ baseHexBody ↔
    -3 ≤ 2*x.1+x.2 ∧ 2*x.1+x.2 ≤ 3 ∧
    -3 ≤ x.1+2*x.2 ∧ x.1+2*x.2 ≤ 3 ∧
    -3 ≤ x.1-x.2 ∧ x.1-x.2 ≤ 3 := by
  rw [baseHexBody_eq_facets]
  norm_num [facetBody,baseHexFacets,Satisfies,evalConstraint]
  constructor <;> rintro ⟨h1,h2,h3,h4,h5,h6⟩ <;>
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

/-- The finite normalized source carrier is exactly the source cell used by the
    independently proved all-plane coverage theorem. -/
theorem standardHexBody_eq_sourceHexCarrier_zero :
    standardHexBody = SpectreGeometry.ReverseExistence.sourceHexCarrier (0,0) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := (baseHexBody_mem_iff y).1 hy
    norm_num [SpectreGeometry.ReverseExistence.sourceHexCarrier,
      SpectreGeometry.ReverseExistence.sourceHexOffset,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
  · intro hx
    have hh : -1 ≤ 2*x.1+x.2 ∧ 2*x.1+x.2 ≤ 1 ∧
        -1 ≤ x.1+2*x.2 ∧ x.1+2*x.2 ≤ 1 ∧
        -1 ≤ x.1-x.2 ∧ x.1-x.2 ≤ 1 := by
      simpa [SpectreGeometry.ReverseExistence.sourceHexCarrier,
        SpectreGeometry.ReverseExistence.sourceHexOffset] using hx
    refine ⟨(3 : ℝ) • x,?_,?_⟩
    · rw [baseHexBody_mem_iff]
      simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
      obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hh
      refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
    · norm_num [smul_smul]

/-- Translating the same fixed carrier gives exactly the integer-center cells. -/
theorem translated_standardHexBody_eq_sourceHexCarrier (c : ℤ × ℤ) :
    (fun x : RealPoint => x + integerPoint c) '' standardHexBody =
      SpectreGeometry.ReverseExistence.sourceHexCarrier c := by
  rw [standardHexBody_eq_sourceHexCarrier_zero]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa [SpectreGeometry.ReverseExistence.sourceHexCarrier,
      integerPoint] using hy
  · intro hx
    refine ⟨x-integerPoint c,?_,?_⟩
    · simpa [SpectreGeometry.ReverseExistence.sourceHexCarrier,
        integerPoint] using hx
    · exact sub_add_cancel _ _

end
end SpectreGeometry.ReverseClusterTriangulation
