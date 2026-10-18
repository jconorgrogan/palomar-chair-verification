module

public import SpectreGeometry.DeformationHomeomorphismGluing
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section


/-! A global integer-grid interpolation tool. All interpolation estimates are
proved from actual neighboring values, not from an assumed geometric tiling. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set
open scoped NNReal

def integerInterpolate (a : ℤ → ℝ) (x : ℝ) : ℝ :=
  let n := ⌊x⌋
  let t := x-n
  (1-t)*a n+t*a (n+1)

@[simp] theorem integerInterpolate_int (a : ℤ → ℝ) (n : ℤ) :
    integerInterpolate a n = a n := by simp [integerInterpolate]

theorem integerInterpolate_on_interval (a : ℤ → ℝ) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc (n : ℝ) (n+1)) :
    integerInterpolate a x = (1-(x-n))*a n+(x-n)*a (n+1) := by
  by_cases he : x = (n:ℝ)+1
  · have he' : x = ((n+1 : ℤ):ℝ) := by push_cast; exact he
    rw [he',integerInterpolate_int]
    push_cast
    ring
  · have hn : ⌊x⌋ = n := Int.floor_eq_iff.mpr ⟨hx.1,lt_of_le_of_ne hx.2 he⟩
    simp [integerInterpolate,hn]

theorem integerIntervals_locallyFinite : LocallyFinite (fun n : ℤ => Icc (n:ℝ) (n+1)) := by
  intro x
  refine ⟨Ioo (x-1) (x+1),Ioo_mem_nhds (by linarith) (by linarith),
    (Set.finite_Icc (⌊x⌋-3) (⌊x⌋+3)).subset ?_⟩
  rintro n ⟨y,hy,hyx⟩
  have hl := Int.floor_le x
  have hu := Int.lt_floor_add_one x
  constructor
  · have h : ((⌊x⌋-3 : ℤ):ℝ) ≤ n := by push_cast; linarith [hy.2,hyx.1]
    exact_mod_cast h
  · have h : (n:ℝ) ≤ ((⌊x⌋+3 : ℤ):ℝ) := by push_cast; linarith [hy.1,hyx.2]
    exact_mod_cast h

theorem integerInterpolate_lipschitz (a : ℤ → ℝ) (K : ℝ≥0)
    (h : ∀ n, |a (n+1)-a n| ≤ K) : LipschitzWith K (integerInterpolate a) := by
  apply Deformation.lipschitz_of_locallyFinite_closed_cover
    (fun n : ℤ => Icc (n:ℝ) (n+1)) integerIntervals_locallyFinite
    (fun _ => isClosed_Icc) (fun x => ⟨⌊x⌋,Int.floor_le x,(Int.lt_floor_add_one x).le⟩)
  intro n
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [integerInterpolate_on_interval a n x hx,integerInterpolate_on_interval a n y hy,
    Real.dist_eq,Real.dist_eq]
  have he : ((1-(x-n))*a n+(x-n)*a (n+1))-
      ((1-(y-n))*a n+(y-n)*a (n+1)) = (a (n+1)-a n)*(x-y) := by ring
  rw [he,abs_mul]
  exact mul_le_mul_of_nonneg_right (h n) (abs_nonneg _)

theorem integerInterpolate_sub (a b : ℤ → ℝ) (x : ℝ) :
    integerInterpolate (fun n => a n-b n) x = integerInterpolate a x-integerInterpolate b x := by
  simp only [integerInterpolate]
  ring

theorem integerInterpolate_smul (a : ℤ → ℝ) (c x : ℝ) :
    integerInterpolate (fun n => c*a n) x = c*integerInterpolate a x := by
  simp only [integerInterpolate]
  ring

@[simp] theorem integerInterpolate_const (c x : ℝ) :
    integerInterpolate (fun _ => c) x = c := by
  simp only [integerInterpolate]
  ring

@[simp] theorem integerInterpolate_identity (x : ℝ) :
    integerInterpolate (fun n => (n:ℝ)) x = x := by
  simp only [integerInterpolate,Int.cast_add,Int.cast_one]
  ring

theorem integerInterpolate_abs_le (a : ℤ → ℝ) (C : ℝ) (h : ∀ n, |a n| ≤ C) (x : ℝ) :
    |integerInterpolate a x| ≤ C := by
  let n := ⌊x⌋
  let t := x-(n:ℝ)
  have ht : 0 ≤ t := Int.fract_nonneg x
  have ht' : t ≤ 1 := (Int.fract_lt_one x).le
  change |(1-t)*a n+t*a (n+1)| ≤ C
  calc
    _ ≤ |(1-t)*a n|+|t*a (n+1)| := abs_add_le _ _
    _ = (1-t)*|a n|+t*|a (n+1)| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1-t),abs_of_nonneg ht]
    _ ≤ (1-t)*C+t*C := add_le_add
      (mul_le_mul_of_nonneg_left (h n) (by linarith)) (mul_le_mul_of_nonneg_left (h (n+1)) ht)
    _ = C := by ring

theorem integerInterpolate_diff_le (a b : ℤ → ℝ) (C : ℝ)
    (h : ∀ n, |a n-b n| ≤ C) (x : ℝ) :
    |integerInterpolate a x-integerInterpolate b x| ≤ C := by
  rw [←integerInterpolate_sub]
  exact integerInterpolate_abs_le _ C h x

/-- Bilinear interpolation on the ordinary complete integer grid. -/
def gridInterpolate (a : ℤ × ℤ → ℝ) (x : ℝ × ℝ) : ℝ :=
  integerInterpolate (fun n => integerInterpolate (fun m => a (n,m)) x.2) x.1

@[simp] theorem gridInterpolate_int (a : ℤ × ℤ → ℝ) (n m : ℤ) :
    gridInterpolate a (n,m) = a (n,m) := by simp [gridInterpolate]

theorem gridInterpolate_horizontal (a : ℤ × ℤ → ℝ) (K : ℝ≥0)
    (h : ∀ n m, |a (n+1,m)-a (n,m)| ≤ K) (y : ℝ) :
    LipschitzWith K (fun x => gridInterpolate a (x,y)) := by
  change LipschitzWith K (integerInterpolate (fun n => integerInterpolate (fun m => a (n,m)) y))
  apply integerInterpolate_lipschitz
  intro n
  exact integerInterpolate_diff_le _ _ K (h n) y

theorem gridInterpolate_vertical (a : ℤ × ℤ → ℝ) (K : ℝ≥0)
    (h : ∀ n m, |a (n,m+1)-a (n,m)| ≤ K) (x : ℝ) :
    LipschitzWith K (fun y => gridInterpolate a (x,y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq]
  apply integerInterpolate_diff_le _ _ (K*dist y z)
  intro n
  simpa only [Real.dist_eq] using (integerInterpolate_lipschitz (fun m => a (n,m)) K (h n)).dist_le_mul y z

theorem gridInterpolate_sub (a b : ℤ × ℤ → ℝ) (x : ℝ × ℝ) :
    gridInterpolate (fun p => a p-b p) x = gridInterpolate a x-gridInterpolate b x := by
  simp only [gridInterpolate,integerInterpolate_sub]

theorem gridInterpolate_smul (a : ℤ × ℤ → ℝ) (c : ℝ) (x : ℝ × ℝ) :
    gridInterpolate (fun p => c*a p) x = c*gridInterpolate a x := by
  simp only [gridInterpolate,integerInterpolate_smul]

@[simp] theorem gridInterpolate_fst (x : ℝ × ℝ) :
    gridInterpolate (fun p => (p.1:ℝ)) x = x.1 := by simp [gridInterpolate]
@[simp] theorem gridInterpolate_snd (x : ℝ × ℝ) :
    gridInterpolate (fun p => (p.2:ℝ)) x = x.2 := by simp [gridInterpolate]

end
end SpectreGeometry.ReverseExistence
