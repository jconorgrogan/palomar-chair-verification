module

public import SpectreGeometry.ReverseIntegerInterpolation
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set

/-- Every point of a uniformly subdivided unit interval lies on one of its
closed subintervals, including the right endpoint. -/
theorem unit_subdivision (n : Nat) (hn : 0 < n) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ j : Fin n, ∃ u ∈ Icc (0:ℝ) 1, t = ((j.val:ℝ)+u)/n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  by_cases he : t = 1
  · refine ⟨⟨n-1,by omega⟩,1,by norm_num,?_⟩
    have hs : ((n-1:Nat):ℝ)+1 = n := by exact_mod_cast (show n-1+1=n by omega)
    rw [he,hs,div_self (ne_of_gt hnR)]
  · have hlt : t < 1 := lt_of_le_of_ne ht.2 he
    have hp : 0 ≤ (n:ℝ)*t := mul_nonneg (le_of_lt hnR) ht.1
    let j : Nat := ⌊(n:ℝ)*t⌋₊
    have hj : j < n := (Nat.floor_lt hp).mpr (by nlinarith)
    have hlow : (j:ℝ) ≤ (n:ℝ)*t := Nat.floor_le hp
    have hhigh : (n:ℝ)*t < (j:ℝ)+1 := Nat.lt_floor_add_one _
    refine ⟨⟨j,hj⟩,(n:ℝ)*t-j,⟨by linarith,by linarith⟩,?_⟩
    apply (eq_div_iff (ne_of_gt hnR)).mpr
    ring

/-- Nested linear parametrizations agree with the uniform subinterval
parameter. This is the exact boundary compatibility used by marked meshes. -/
theorem uniform_lineMap (a b : ℝ×ℝ) (n : Nat) (hn : 0 < n) (j : Nat) (u : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap a b ((j:ℝ)/n))
        (AffineMap.lineMap a b (((j:ℝ)+1)/n)) u =
      AffineMap.lineMap a b (((j:ℝ)+u)/n) := by
  ext <;> simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,
    Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
    smul_eq_mul] <;> ring

end
end SpectreGeometry.ReverseExistence
