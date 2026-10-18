module

public import SpectreGeometry.PolygonProductKeyReferenceRigidity
public import SpectreGeometry.PolygonProductKeyFrames
public import PhysicalRegistration.KeyTent

@[expose] public section


namespace SpectreGeometry.ProductKeyReference
open SparseMonotiles SparseMonotiles.Contact PhysicalRegistration
noncomputable section

def coordinateEnvelope (x : Point 4) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 =>
    min (1 + (productKeyPrime i false : ℝ) * x i.castSucc / productKeyEta)
      (1 - (productKeyPrime i true : ℝ) * x i.castSucc / productKeyEta))

def referenceHeight (j : Fin 2) : ℝ := productKeyEta * (j.val + 1) / productKeyN

def coordinateFootprint (x : Point 4) : Prop := ∀ i : Fin 3,
  -productKeyEta / (productKeyPrime i false : ℝ) ≤ x i.castSucc ∧
  x i.castSucc ≤ productKeyEta / (productKeyPrime i true : ℝ)

theorem recipe_prime_pos (i : Fin 3) (b : Bool) : 0 < (productKeyPrime i b : ℝ) := by
  fin_cases i <;> cases b <;> norm_num [productKeyPrime, productKeyPrimePairs]

theorem envelope_nonneg_iff (x : Point 4) : 0 ≤ coordinateEnvelope x ↔ coordinateFootprint x := by
  unfold coordinateEnvelope coordinateFootprint
  rw [Finset.le_inf'_iff]
  simp only [Finset.mem_univ, forall_const, le_min_iff]
  apply forall_congr'
  intro i
  have hm := recipe_prime_pos i false
  have hp := recipe_prime_pos i true
  have he : 0 < productKeyEta := by norm_num [productKeyEta]
  rw [div_le_iff₀ hm, le_div_iff₀ hp]
  constructor
  · rintro ⟨h1,h2⟩
    have h1' := (le_div_iff₀ he).mp (show -1 ≤ (productKeyPrime i false : ℝ) * x i.castSucc / productKeyEta by linarith)
    have h2' := (div_le_iff₀ he).mp (show (productKeyPrime i true : ℝ) * x i.castSucc / productKeyEta ≤ 1 by linarith)
    constructor <;> nlinarith
  · rintro ⟨h1,h2⟩
    have h1' : -1 ≤ (productKeyPrime i false : ℝ) * x i.castSucc / productKeyEta :=
      (le_div_iff₀ he).mpr (by nlinarith)
    have h2' : (productKeyPrime i true : ℝ) * x i.castSucc / productKeyEta ≤ 1 :=
      (div_le_iff₀ he).mpr (by nlinarith)
    constructor <;> linarith

theorem reference_height_pos (j : Fin 2) : 0 < referenceHeight j := by
  fin_cases j <;> norm_num [referenceHeight, productKeyEta, productKeyN]

theorem coordinate_tent_iff (j : Fin 2) (x : Point 4) :
    coordinateFootprint x ∧ 0 ≤ x 3 ∧ x 3 ≤ referenceHeight j * max 0 (coordinateEnvelope x) ↔
    0 ≤ x 3 ∧ ∀ i : Fin 3,
      x 3 ≤ referenceHeight j * (1 + (productKeyPrime i false : ℝ) * x i.castSucc / productKeyEta) ∧
      x 3 ≤ referenceHeight j * (1 - (productKeyPrime i true : ℝ) * x i.castSucc / productKeyEta) := by
  have hh := reference_height_pos j
  constructor
  · rintro ⟨hf,hz,hbound⟩
    rw [max_eq_right ((envelope_nonneg_iff x).mpr hf)] at hbound
    refine ⟨hz,fun i => ?_⟩
    have hm := Finset.inf'_le (fun i : Fin 3 =>
      min (1 + (productKeyPrime i false : ℝ) * x i.castSucc / productKeyEta)
        (1 - (productKeyPrime i true : ℝ) * x i.castSucc / productKeyEta)) (Finset.mem_univ i)
    change coordinateEnvelope x ≤ min _ _ at hm
    exact ⟨hbound.trans (mul_le_mul_of_nonneg_left ((le_min_iff.mp hm).1) hh.le),
      hbound.trans (mul_le_mul_of_nonneg_left ((le_min_iff.mp hm).2) hh.le)⟩
  · rintro ⟨hz,hbounds⟩
    have hdiv : x 3 / referenceHeight j ≤ coordinateEnvelope x := by
      unfold coordinateEnvelope
      rw [Finset.le_inf'_iff]
      intro i _
      apply le_min
      · exact (div_le_iff₀ hh).mpr (by simpa [mul_comm] using (hbounds i).1)
      · exact (div_le_iff₀ hh).mpr (by simpa [mul_comm] using (hbounds i).2)
    have hm : 0 ≤ coordinateEnvelope x := (div_nonneg hz hh.le).trans hdiv
    refine ⟨(envelope_nonneg_iff x).mp hm,hz,?_⟩
    rw [max_eq_right hm]
    simpa [mul_comm] using (div_le_iff₀ hh).mp hdiv

end
end SpectreGeometry.ProductKeyReference
