module

public import SpectreGeometry.PolygonProductReferenceTent

@[expose] public section


namespace SpectreGeometry.ProductKeyReference
open SparseMonotiles SparseMonotiles.Contact
noncomputable section

theorem reference_height_eq (j : Fin 2) :
    keyPyramidHeight ((referenceBox j).toKeyData referenceDenominator) = referenceHeight j := by
  fin_cases j <;> norm_num [keyPyramidHeight, referenceBox, referenceDenominator,
    BoxKey.toKeyData, rationalVertex, referenceHeight, productKeyEta, productKeyN]

theorem reference_lo_eq (j : Fin 2) (i : Fin 3) :
    keyPyramidLo ((referenceBox j).toKeyData referenceDenominator) i =
      -productKeyEta / (productKeyPrime i false : ℝ) := by
  fin_cases j <;> fin_cases i <;> norm_num [keyPyramidLo, referenceBox, referenceDenominator,
    BoxKey.toKeyData, rationalVertex, productKeyEta, productKeyPrime, productKeyPrimePairs]

theorem reference_hi_eq (j : Fin 2) (i : Fin 3) :
    keyPyramidHi ((referenceBox j).toKeyData referenceDenominator) i =
      productKeyEta / (productKeyPrime i true : ℝ) := by
  fin_cases j <;> fin_cases i <;> norm_num [keyPyramidHi, referenceBox, referenceDenominator,
    BoxKey.toKeyData, rationalVertex, productKeyEta, productKeyPrime, productKeyPrimePairs]

theorem reference_apex_eq (j : Fin 2) (i : Fin 3) :
    keyPyramidApex ((referenceBox j).toKeyData referenceDenominator) i = 0 := by
  fin_cases j <;> fin_cases i <;> norm_num [keyPyramidApex, referenceBox, referenceDenominator,
    BoxKey.toKeyData, rationalVertex]

theorem reference_side_iff (j : Fin 2) (i : Fin 3) (z t : ℝ) :
    ((referenceHeight j-z)*(-productKeyEta/(productKeyPrime i false : ℝ)) ≤ referenceHeight j*t ∧
     referenceHeight j*t ≤ (referenceHeight j-z)*(productKeyEta/(productKeyPrime i true : ℝ))) ↔
    (z ≤ referenceHeight j*(1+(productKeyPrime i false : ℝ)*t/productKeyEta) ∧
     z ≤ referenceHeight j*(1-(productKeyPrime i true : ℝ)*t/productKeyEta)) := by
  fin_cases j <;> fin_cases i <;>
    norm_num [referenceHeight,productKeyEta,productKeyN,productKeyPrime,productKeyPrimePairs] <;>
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> nlinarith

theorem reference_mem_iff_branch_bounds (j : Fin 2) (x : Point 4) :
    x ∈ referenceSolid j ↔ 0 ≤ x 3 ∧ ∀ i : Fin 3,
      x 3 ≤ referenceHeight j*(1+(productKeyPrime i false : ℝ)*x i.castSucc/productKeyEta) ∧
      x 3 ≤ referenceHeight j*(1-(productKeyPrime i true : ℝ)*x i.castSucc/productKeyEta) := by
  unfold referenceSolid
  rw [mem_keySolid_iff_pyramidHalfspaces _
    (by norm_num [referenceBox,BoxKey.toKeyData,rationalVertex,Fin.last])
    (by norm_num [referenceBox,BoxKey.toKeyData,rationalVertex,Fin.last]) (height_pos j),
    mem_pyramidHalfspaces]
  simp only [pointPyramidEquiv_fst,pointPyramidEquiv_snd,reference_height_eq,
    reference_lo_eq,reference_hi_eq,reference_apex_eq,mul_zero,add_zero]
  change (0 ≤ x 3 ∧ x 3 ≤ referenceHeight j ∧ ∀ i : Fin 3,
    (referenceHeight j-x 3)*(-productKeyEta/(productKeyPrime i false : ℝ)) ≤ referenceHeight j*x i.castSucc ∧
    referenceHeight j*x i.castSucc ≤ (referenceHeight j-x 3)*(productKeyEta/(productKeyPrime i true : ℝ))) ↔ _
  simp only [reference_side_iff]
  constructor
  · rintro ⟨hz,_,hb⟩
    exact ⟨hz,hb⟩
  · rintro ⟨hz,hb⟩
    refine ⟨hz,?_,hb⟩
    have h0 := hb 0
    fin_cases j <;>
      norm_num [referenceHeight,productKeyEta,productKeyN,productKeyPrime,productKeyPrimePairs] at h0 ⊢ <;>
      nlinarith [h0.1,h0.2]

/-- The exact reference convex hull equals the positive tent over its actual
asymmetric footprint. The footprint restriction prevents the zero extension
from adding the entire outside base hyperplane. -/
theorem reference_mem_iff_tent (j : Fin 2) (x : Point 4) :
    x ∈ referenceSolid j ↔ coordinateFootprint x ∧ 0 ≤ x 3 ∧
      x 3 ≤ referenceHeight j * max 0 (coordinateEnvelope x) := by
  rw [reference_mem_iff_branch_bounds,coordinate_tent_iff]

end
end SpectreGeometry.ProductKeyReference
