module

public import SpectreGeometry.ReverseFinitePLInteger
public import SpectreGeometry.ReverseClusterTriangulationHexBinding

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set ReverseClusterTriangulation

def scalarHomeomorph (a : ℝ) (ha : a ≠ 0) : Plane ≃ₜ Plane where
  toFun x := a • x
  invFun x := a⁻¹ • x
  left_inv x := by simp only [smul_smul,inv_mul_cancel₀ ha,one_smul]
  right_inv x := by simp only [smul_smul,mul_inv_cancel₀ ha,one_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem scalarHomeomorph_apply (a : ℝ) (ha : a ≠ 0) (x : Plane) :
    scalarHomeomorph a ha x = a • x := rfl

/-- Normalize an actual dilated closed hex carrier, reusing the independently
checked six-fan carrier equality. -/
def sourceHexFromDilatedHomeomorph (n : Int) (hn : 0 < n) :
    facetBody (baseHexFacets.map (dilateFacet n)) ≃ₜ
      ReverseExistence.sourceHexCarrier (0,0) :=
  ((scalarHomeomorph (1/(3*(n:ℝ))) (by
    apply one_div_ne_zero
    exact mul_ne_zero (by norm_num) (by exact_mod_cast (ne_of_gt hn)))).image
      (facetBody (baseHexFacets.map (dilateFacet n)))).trans
    (Homeomorph.setCongr ((normalize_dilated_hex n hn).trans
      standardHexBody_eq_sourceHexCarrier_zero))

end
end SpectreGeometry.ReverseFinitePL
