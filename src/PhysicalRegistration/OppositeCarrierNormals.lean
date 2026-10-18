module

public import PhysicalRegistration.BasePlaneRigidity
public import PhysicalRegistration.CreaseConnectivity

@[expose] public section

/-! The material sign fixes the remaining carrier-normal ambiguity. A
nonzero actual apex cannot lie simultaneously on equal-normal graphs whose
signed coefficients oppose and whose base centers agree. -/
namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

/-- Every actual tent height has the sign of its signed native coefficient. -/
theorem coefficient_mul_siteHeight_nonneg {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (u : Site m) (x : Space m) :
    0 ≤ (a.value u : ℝ) * siteHeight a u x := by
  have hprofile := (native_profile_range J u (x - siteCenter u)).1
  have hN : 0 < (denominator m J : ℝ) := by exact_mod_cast (denominator_prime m J).pos
  unfold siteHeight keyHeight
  rw [show (a.value u : ℝ) *
      (eta m * (a.value u : ℝ) / denominator m J *
        keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) (x - siteCenter u)) =
      (eta m / denominator m J) * (a.value u : ℝ)^2 *
        keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) (x - siteCenter u) by ring]
  exact mul_nonneg (mul_nonneg (div_nonneg (eta_pos m).le hN.le) (sq_nonneg _)) hprofile

/-- In dimension at least three the actual apex belongs to a distinct-axis
side crease, hence to the closed crease complex. -/
theorem keyApex_mem_creaseComplex {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) : keyApex a u ∈ creaseComplex a u := by
  let s : Side m := (⟨0, by omega⟩, false)
  let t : Side m := (⟨1, by omega⟩, false)
  apply sideCrease_subset_creaseComplex a u s t (by simp [s, t])
  exact ⟨keyApex_mem_sideFace a u s, keyApex_mem_sideFace a u t⟩

/-- Equal placed centers and opposite signed coefficients rule out equal
carrier normals for a whole-complex containment. This uses an actual apex
point and literal graph membership, not an assumed choice of material side. -/
theorem whole_crease_opposite_normal_of_centers
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J)
    (u v : Site m) (f g : Space m ≃ᵢ Space m)
    (hbase : ∀ s : Side m, f '' baseCrease a u s = g '' baseCrease a v s)
    (hcenter : f (siteCenter u) = g (siteCenter v))
    (hcoeff : a.value v = -a.value u)
    (hcomplex : f '' creaseComplex a u ⊆ g '' creaseComplex a v) :
    placedNormal g (outward v.1) = -placedNormal f (outward u.1) := by
  rcases labelled_baseCreases_outward_eq_or_neg hm a u v f g hbase with heq | hneg
  · have hx : f (keyApex a u) ∈ g '' creaseComplex a v :=
      hcomplex ⟨keyApex a u, keyApex_mem_creaseComplex hm a u, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hx
    have hzkey := creaseComplex_subset_keyGraph a v hz
    have hn : normalCoord v z = eta m * (a.value u : ℝ) / denominator m J := by
      have hscalar : ⟪placedNormal g (outward v.1), g z - g (siteCenter v)⟫_ℝ =
          ⟪placedNormal f (outward u.1), f (keyApex a u) - f (siteCenter u)⟫_ℝ := by
        rw [heq, hzx, hcenter]
      rw [placedNormal_inner_sub, placedNormal_inner_sub] at hscalar
      simp only [g.symm_apply_apply, f.symm_apply_apply] at hscalar
      change normalCoord v z = normalCoord u (keyApex a u) at hscalar
      simpa [keyApex] using hscalar
    have hsign := coefficient_mul_siteHeight_nonneg a v z
    rw [← hzkey.2, hn, hcoeff, Int.cast_neg] at hsign
    have hN : 0 < (denominator m J : ℝ) := by exact_mod_cast (denominator_prime m J).pos
    have hau : (a.value u : ℝ) ≠ 0 := by exact_mod_cast a.nonzero u
    have hpositive : 0 < (eta m / denominator m J) * (a.value u : ℝ)^2 :=
      mul_pos (div_pos (eta_pos m) hN) (sq_pos_of_ne_zero hau)
    have heqprod : -(a.value u : ℝ) * (eta m * (a.value u : ℝ) / denominator m J) =
        -((eta m / denominator m J) * (a.value u : ℝ)^2) := by ring
    rw [heqprod] at hsign
    linarith
  · exact hneg

#print axioms coefficient_mul_siteHeight_nonneg
#print axioms keyApex_mem_creaseComplex
#print axioms whole_crease_opposite_normal_of_centers
end
end PhysicalRegistration.NativeChair
