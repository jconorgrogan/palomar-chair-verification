module

public import SpectreGeometry.ReverseIntegerInterpolation

@[expose] public section


/-! Actual coverage of the real axial plane by the fixed regular source hexagons.
The unit-square proof uses only linear inequalities, not an assumed tiling. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section

def sourceHexOffset (u v : ℝ) : Prop :=
  -1 ≤ 2*u+v ∧ 2*u+v ≤ 1 ∧ -1 ≤ u+2*v ∧ u+2*v ≤ 1 ∧
  -1 ≤ u-v ∧ u-v ≤ 1

def sourceHexCarrier (c : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {p | sourceHexOffset (p.1-c.1) (p.2-c.2)}

theorem sourceHex_unit_square_cover (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∃ a b : ℤ, (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧
      sourceHexOffset (x-a) (y-b) := by
  by_cases hxy : y ≤ x
  · by_cases h0 : 2*x+y ≤ 1
    · refine ⟨0,0,Or.inl rfl,Or.inl rfl,?_⟩
      simp only [sourceHexOffset,Int.cast_zero,sub_zero]
      refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
    · by_cases h1 : x+2*y ≤ 2
      · refine ⟨1,0,Or.inr rfl,Or.inl rfl,?_⟩
        simp only [sourceHexOffset,Int.cast_one,Int.cast_zero,sub_zero]
        refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
      · refine ⟨1,1,Or.inr rfl,Or.inr rfl,?_⟩
        simp only [sourceHexOffset,Int.cast_one]
        refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
  · by_cases h0 : x+2*y ≤ 1
    · refine ⟨0,0,Or.inl rfl,Or.inl rfl,?_⟩
      simp only [sourceHexOffset,Int.cast_zero,sub_zero]
      refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
    · by_cases h1 : 2*x+y ≤ 2
      · refine ⟨0,1,Or.inl rfl,Or.inr rfl,?_⟩
        simp only [sourceHexOffset,Int.cast_one,Int.cast_zero,sub_zero]
        refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
      · refine ⟨1,1,Or.inr rfl,Or.inr rfl,?_⟩
        simp only [sourceHexOffset,Int.cast_one]
        refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem sourceHex_plane_cover (p : ℝ × ℝ) : ∃ c : ℤ × ℤ, p ∈ sourceHexCarrier c := by
  have hx0 : 0 ≤ p.1-(⌊p.1⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le p.1)
  have hx1 : p.1-(⌊p.1⌋ : ℝ) ≤ 1 := by linarith [Int.lt_floor_add_one p.1]
  have hy0 : 0 ≤ p.2-(⌊p.2⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le p.2)
  have hy1 : p.2-(⌊p.2⌋ : ℝ) ≤ 1 := by linarith [Int.lt_floor_add_one p.2]
  obtain ⟨a,b,_,_,h⟩ := sourceHex_unit_square_cover
    (p.1-(⌊p.1⌋ : ℝ)) (p.2-(⌊p.2⌋ : ℝ)) hx0 hx1 hy0 hy1
  refine ⟨(⌊p.1⌋+a,⌊p.2⌋+b),?_⟩
  change sourceHexOffset (p.1-((⌊p.1⌋+a : ℤ) : ℝ)) (p.2-((⌊p.2⌋+b : ℤ) : ℝ))
  simpa only [Int.cast_add,sub_add_eq_sub_sub] using h

end
end SpectreGeometry.ReverseExistence
