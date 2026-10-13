module

public import PhysicalRegistration.CarrierTransverse

@[expose] public section

/-!
# A concrete inward direction inside the transverse normal span

At an untouched carrier boundary point, move only its active integer-plane
coordinates toward 1/2. The resulting nonzero vector is in every subspace
containing those coordinate normals, and its positive short ray enters the
actual carrier interior. Every active coordinate changes strictly. This is
the native positivity input for ordinary planar sectors.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

def activeCarrierDirection {m : ℕ} (x : Space m) : Space m :=
  ∑ i ∈ activeCarrierAxes x, (1 / 2 - x i) • EuclideanSpace.single i (1 : ℝ)

theorem activeCarrierDirection_coordinate {m : ℕ} (x : Space m) (i : Fin (m + 1)) :
    activeCarrierDirection x i = if i ∈ activeCarrierAxes x then 1 / 2 - x i else 0 := by
  have h : ⟪EuclideanSpace.single i (1 : ℝ), activeCarrierDirection x⟫_ℝ =
      if i ∈ activeCarrierAxes x then 1 / 2 - x i else 0 := by
    simp [activeCarrierDirection, inner_sum,
      EuclideanSpace.inner_single_left]
  simpa [EuclideanSpace.inner_single_left] using h

theorem activeCarrierDirection_mem {m : ℕ} (x : Space m) (K : Submodule ℝ (Space m))
    (hK : ∀ i ∈ activeCarrierAxes x, EuclideanSpace.single i (1 : ℝ) ∈ K) :
    activeCarrierDirection x ∈ K := by
  apply Submodule.sum_mem
  intro i hi
  exact K.smul_mem _ (hK i hi)

theorem activeCarrierDirection_strict {m : ℕ} (x : Space m) (i : Fin (m + 1))
    (hi : i ∈ activeCarrierAxes x) : activeCarrierDirection x i ≠ 0 := by
  rw [activeCarrierDirection_coordinate, ite_eq_left hi]
  have h : x i = 0 ∨ x i = 1 ∨ x i = 2 := by
    simpa [activeCarrierAxes] using hi
  rcases h with h | h | h <;> rw [h] <;> norm_num

theorem activeCarrierDirection_ne_zero {m : ℕ} (x : Space m)
    (hx : x ∈ frontier (carrier m)) : activeCarrierDirection x ≠ 0 := by
  obtain ⟨i, hi⟩ := carrier_frontier_coordinate x hx
  have hmem : i ∈ activeCarrierAxes x := by simpa [activeCarrierAxes] using hi
  intro hz
  exact activeCarrierDirection_strict x i hmem (by simp [hz])

/-- The ray moves only active coordinates. All inactive coordinates already
have strict margins, so no unknown radius or regularity certificate is used. -/
theorem activeCarrierDirection_ray_mem_interior {m : ℕ} (x : Space m)
    (hx : x ∈ carrier m) (t : ℝ) (ht : 0 < t) (htone : t ≤ 1) :
    x + t • activeCarrierDirection x ∈ interior (carrier m) := by
  have hb := (mem_carrier_iff x).mp hx
  apply strict_carrier_mem_interior
  · intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [activeCarrierDirection_coordinate]
    by_cases hi : i ∈ activeCarrierAxes x
    · rw [ite_eq_left hi]
      have hlow := mul_nonneg (sub_nonneg.mpr htone) (hb.1 i).1
      have hupp := mul_le_mul_of_nonneg_left (hb.1 i).2 (sub_nonneg.mpr htone)
      constructor <;> nlinarith
    · rw [ite_eq_right hi, mul_zero, add_zero]
      have hne : x i ≠ 0 ∧ x i ≠ 1 ∧ x i ≠ 2 := by
        simpa [activeCarrierAxes, not_or] using hi
      exact ⟨lt_of_le_of_ne (hb.1 i).1 (Ne.symm hne.1),
        lt_of_le_of_ne (hb.1 i).2 hne.2.2⟩
  · obtain ⟨i, hi⟩ := hb.2
    refine ⟨i, ?_⟩
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [activeCarrierDirection_coordinate]
    by_cases hmem : i ∈ activeCarrierAxes x
    · rw [ite_eq_left hmem]
      have hupp := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr htone)
      nlinarith
    · rw [ite_eq_right hmem, mul_zero, add_zero]
      have hne : x i ≠ 1 := by
        intro he
        exact hmem (by simp [activeCarrierAxes, he])
      exact lt_of_le_of_ne hi hne

/-- The actual transverse span has a nonzero strict inward carrier direction.
Every active coordinate is nonzero along it, so this direction is off all
ordinary boundary rays when restricted to that span. -/
theorem carrier_transverse_interior_direction {m : ℕ} (x p q : Space m)
    (hx : x ∈ frontier (carrier m))
    (hspan : ∀ i ∈ activeCarrierAxes x,
      EuclideanSpace.single i (1 : ℝ) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    ∃ v ∈ Submodule.span ℝ ({p, q} : Set (Space m)), v ≠ 0 ∧
      (∀ i ∈ activeCarrierAxes x, v i ≠ 0) ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 → x + t • v ∈ interior (carrier m) := by
  refine ⟨activeCarrierDirection x, activeCarrierDirection_mem x _ hspan,
    activeCarrierDirection_ne_zero x hx, activeCarrierDirection_strict x, ?_⟩
  exact activeCarrierDirection_ray_mem_interior x ((carrier_isClosed m).frontier_subset hx)

#print axioms activeCarrierDirection_coordinate
#print axioms activeCarrierDirection_mem
#print axioms activeCarrierDirection_ne_zero
#print axioms activeCarrierDirection_ray_mem_interior
#print axioms carrier_transverse_interior_direction
end
end PhysicalRegistration.NativeChair
