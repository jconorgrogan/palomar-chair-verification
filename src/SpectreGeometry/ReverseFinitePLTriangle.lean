module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section


/-! A nondegenerate triangle supplies an explicitly invertible affine chart.
No global mesh embedding is assumed in this module. -/
namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set

abbrev Plane := ℝ × ℝ

def triangleDet (v : Fin 3 → Plane) : ℝ :=
  ((v 1).1-(v 0).1)*((v 2).2-(v 0).2)-((v 2).1-(v 0).1)*((v 1).2-(v 0).2)

def triangleLinear (v : Fin 3 → Plane) : Plane →ₗ[ℝ] Plane where
  toFun x := (x.1*((v 1).1-(v 0).1)+x.2*((v 2).1-(v 0).1),
    x.1*((v 1).2-(v 0).2)+x.2*((v 2).2-(v 0).2))
  map_add' x y := by ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> ring
  map_smul' c x := by
    ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,RingHom.id_apply] <;> ring

def triangleAffine (v : Fin 3 → Plane) : Plane →ᵃ[ℝ] Plane where
  toFun x := v 0 + triangleLinear v x
  linear := triangleLinear v
  map_vadd' p x := by simp only [vadd_eq_add,map_add]; abel

@[simp] theorem triangleLinear_apply (v : Fin 3 → Plane) (x : Plane) :
    triangleLinear v x = (x.1*((v 1).1-(v 0).1)+x.2*((v 2).1-(v 0).1),
      x.1*((v 1).2-(v 0).2)+x.2*((v 2).2-(v 0).2)) := rfl

@[simp] theorem triangleAffine_apply (v : Fin 3 → Plane) (x : Plane) :
    triangleAffine v x = v 0 + triangleLinear v x := rfl

def triangleInverse (v : Fin 3 → Plane) (x : Plane) : Plane :=
  (((x.1-(v 0).1)*((v 2).2-(v 0).2)-(x.2-(v 0).2)*((v 2).1-(v 0).1))/triangleDet v,
   (((v 1).1-(v 0).1)*(x.2-(v 0).2)-((v 1).2-(v 0).2)*(x.1-(v 0).1))/triangleDet v)

theorem triangleInverse_left (v : Fin 3 → Plane) (h : triangleDet v ≠ 0) (x : Plane) :
    triangleInverse v (triangleAffine v x) = x := by
  ext <;> simp only [triangleInverse,triangleAffine_apply,triangleLinear_apply,Prod.fst_add,Prod.snd_add] <;>
    field_simp [h] <;> simp only [triangleDet] <;> ring

theorem triangleInverse_right (v : Fin 3 → Plane) (h : triangleDet v ≠ 0) (x : Plane) :
    triangleAffine v (triangleInverse v x) = x := by
  ext <;> simp only [triangleInverse,triangleAffine_apply,triangleLinear_apply,Prod.fst_add,Prod.snd_add] <;>
    field_simp [h] <;> simp only [triangleDet] <;> ring

def triangleFrame (v : Fin 3 → Plane) (h : triangleDet v ≠ 0) : Plane ≃ᵃ[ℝ] Plane :=
  AffineEquiv.ofBijective ⟨Function.LeftInverse.injective (triangleInverse_left v h),
    Function.RightInverse.surjective (triangleInverse_right v h)⟩

@[simp] theorem triangleFrame_apply (v : Fin 3 → Plane) (h : triangleDet v ≠ 0) (x : Plane) :
    triangleFrame v h x = triangleAffine v x := rfl

def standardVertex : Fin 3 → Plane := ![(0,0),(1,0),(0,1)]

@[simp] theorem triangleFrame_vertex (v : Fin 3 → Plane) (h : triangleDet v ≠ 0) (i : Fin 3) :
    triangleFrame v h (standardVertex i) = v i := by
  fin_cases i <;> ext <;> simp [standardVertex] <;> ring

def triangleEquiv (s t : Fin 3 → Plane) (hs : triangleDet s ≠ 0) (ht : triangleDet t ≠ 0) :
    Plane ≃ᵃ[ℝ] Plane := (triangleFrame s hs).symm.trans (triangleFrame t ht)

@[simp] theorem triangleEquiv_vertex (s t : Fin 3 → Plane)
    (hs : triangleDet s ≠ 0) (ht : triangleDet t ≠ 0) (i : Fin 3) :
    triangleEquiv s t hs ht (s i) = t i := by
  change triangleFrame t ht ((triangleFrame s hs).symm (s i)) = t i
  have hi : (triangleFrame s hs).symm (s i) = standardVertex i := by
    apply (triangleFrame s hs).injective
    rw [AffineEquiv.apply_symm_apply,triangleFrame_vertex]
  rw [hi,triangleFrame_vertex]

@[simp] theorem triangleEquiv_symm_vertex (s t : Fin 3 → Plane)
    (hs : triangleDet s ≠ 0) (ht : triangleDet t ≠ 0) (i : Fin 3) :
    (triangleEquiv s t hs ht).symm (t i) = s i := by
  rw [←triangleEquiv_vertex s t hs ht i,AffineEquiv.symm_apply_apply]

def triangleHull (v : Fin 3 → Plane) : Set Plane := convexHull ℝ (range v)

theorem triangleHull_closed (v : Fin 3 → Plane) : IsClosed (triangleHull v) :=
  ((finite_range v).isCompact_convexHull ℝ).isClosed

theorem triangleEquiv_image_hull (s t : Fin 3 → Plane)
    (hs : triangleDet s ≠ 0) (ht : triangleDet t ≠ 0) :
    triangleEquiv s t hs ht '' triangleHull s = triangleHull t := by
  change (triangleEquiv s t hs ht).toAffineMap '' convexHull ℝ (range s) = _
  rw [AffineMap.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,(triangleEquiv_vertex s t hs ht i).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨s i,⟨i,rfl⟩,triangleEquiv_vertex s t hs ht i⟩

end
end SpectreGeometry.ReverseFinitePL
