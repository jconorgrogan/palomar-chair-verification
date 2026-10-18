module

public import ProductClosure.CarrierTransverse

@[expose] public section

/-! Strict inward rays derived from a containing cell, without a global star-center. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

/-- Only active coordinates move, toward the center of the chosen cell. -/
def activeCarrierDirection (c : Polycube.Cell S) (x : Space m) : Space m :=
  ∑ i ∈ activeCarrierAxes S x,
    ((c.val i : ℝ) + 1 / 2 - x i) • EuclideanSpace.single i (1 : ℝ)

theorem activeCarrierDirection_coordinate (c : Polycube.Cell S) (x : Space m)
    (i : Fin (m + 1)) :
    activeCarrierDirection c x i =
      if i ∈ activeCarrierAxes S x then (c.val i : ℝ) + 1 / 2 - x i else 0 := by
  have h : ⟪EuclideanSpace.single i (1 : ℝ), activeCarrierDirection c x⟫_ℝ =
      if i ∈ activeCarrierAxes S x then (c.val i : ℝ) + 1 / 2 - x i else 0 := by
    simp [activeCarrierDirection, inner_sum, EuclideanSpace.inner_single_left]
  simpa [EuclideanSpace.inner_single_left] using h

theorem activeCarrierDirection_mem (c : Polycube.Cell S) (x : Space m)
    (K : Submodule ℝ (Space m))
    (hK : ∀ i ∈ activeCarrierAxes S x, EuclideanSpace.single i (1 : ℝ) ∈ K) :
    activeCarrierDirection c x ∈ K := by
  apply Submodule.sum_mem
  intro i hi
  exact K.smul_mem _ (hK i hi)

/-- Every active coordinate is integer, so it cannot equal any cell's half-integer center. -/
theorem activeCarrierDirection_strict (c : Polycube.Cell S) (x : Space m)
    (i : Fin (m + 1)) (hi : i ∈ activeCarrierAxes S x) :
    activeCarrierDirection c x i ≠ 0 := by
  rw [activeCarrierDirection_coordinate, ite_eq_left hi]
  obtain ⟨d, hd⟩ := (mem_activeCarrierAxes x i).mp hi
  have hint : ∃ k : ℤ, x i = (k : ℝ) := by
    rcases hd with hd | hd
    · exact ⟨d.val i, hd⟩
    · exact ⟨d.val i + 1, by simpa using hd⟩
  obtain ⟨k, hk⟩ := hint
  rw [hk]
  intro he
  have hlt : (c.val i : ℝ) < (k : ℝ) := by linarith
  have hle : (k : ℝ) < (c.val i : ℝ) + 1 := by linarith
  have hlt' : c.val i < k := by exact_mod_cast hlt
  have hle' : k < c.val i + 1 := by exact_mod_cast hle
  omega

theorem activeCarrierDirection_ne_zero (c : Polycube.Cell S) (x : Space m)
    (hx : x ∈ frontier (Polycube.carrier S)) : activeCarrierDirection c x ≠ 0 := by
  obtain ⟨d, i, hi⟩ := carrier_frontier_coordinate S x hx
  have hmem : i ∈ activeCarrierAxes S x := (mem_activeCarrierAxes x i).mpr ⟨d, hi⟩
  intro hz
  exact activeCarrierDirection_strict c x i hmem (by simp [hz])

/-- The containing cell supplies a genuine interior ray. Inactive coordinates
already lie strictly between this cell's endpoints. -/
theorem activeCarrierDirection_ray_mem_interior (c : Polycube.Cell S) (x : Space m)
    (hx : x ∈ Polycube.latticeCell c.val) (t : ℝ) (ht : 0 < t) (htone : t ≤ 1) :
    x + t • activeCarrierDirection c x ∈ interior (Polycube.carrier S) := by
  apply strict_cell_mem_interior_carrier c
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [activeCarrierDirection_coordinate]
  by_cases hi : i ∈ activeCarrierAxes S x
  · rw [ite_eq_left hi]
    have hlo := mul_nonneg (sub_nonneg.mpr htone) (sub_nonneg.mpr (hx i).1)
    have hup := mul_nonneg (sub_nonneg.mpr htone) (sub_nonneg.mpr (hx i).2)
    constructor <;> nlinarith
  · rw [ite_eq_right hi, mul_zero, add_zero]
    have hlo : x i ≠ (c.val i : ℝ) := fun he => hi
      ((mem_activeCarrierAxes x i).mpr ⟨c, Or.inl he⟩)
    have hup : x i ≠ (c.val i : ℝ) + 1 := fun he => hi
      ((mem_activeCarrierAxes x i).mpr ⟨c, Or.inr he⟩)
    exact ⟨lt_of_le_of_ne (hx i).1 (Ne.symm hlo), lt_of_le_of_ne (hx i).2 hup⟩

theorem carrier_transverse_interior_direction (S : Finset (Polycube.LatticeIndex (m + 1)))
    (x p q : Space m) (hx : x ∈ frontier (Polycube.carrier S))
    (hspan : ∀ i ∈ activeCarrierAxes S x,
      EuclideanSpace.single i (1 : ℝ) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    ∃ v ∈ Submodule.span ℝ ({p, q} : Set (Space m)), v ≠ 0 ∧
      (∀ i ∈ activeCarrierAxes S x, v i ≠ 0) ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 → x + t • v ∈ interior (Polycube.carrier S) := by
  obtain ⟨z, hz, hxz⟩ := (Polycube.mem_carrier_iff S x).mp
    ((carrier_isClosed S).frontier_subset hx)
  let c : Polycube.Cell S := ⟨z, hz⟩
  exact ⟨activeCarrierDirection c x, activeCarrierDirection_mem c x _ hspan,
    activeCarrierDirection_ne_zero c x hx, activeCarrierDirection_strict c x,
    activeCarrierDirection_ray_mem_interior c x hxz⟩

#print axioms activeCarrierDirection_strict
#print axioms activeCarrierDirection_ray_mem_interior
#print axioms carrier_transverse_interior_direction
end
end ProductClosure.NativeCompiler
