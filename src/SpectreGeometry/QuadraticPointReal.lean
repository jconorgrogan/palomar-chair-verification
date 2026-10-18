module

public import SpectreGeometry.QuadraticPointData
public import SpectreGeometry.QuadraticCoordinates
public import SpectreGeometry.CyclicRotations

@[expose] public section


namespace SpectreGeometry
noncomputable section
open QuadraticCoordinates

def rationalPointEval (p : RationalQuadraticPoint) : RealPoint := (eval p.1,eval p.2)

theorem ratQuadAdd_eval (x y : RationalQuadratic) : eval (ratQuadAdd x y) = eval x+eval y := by
  simp only [eval,ratQuadAdd,Rat.cast_add]
  ring

theorem ratQuadSub_eval (x y : RationalQuadratic) : eval (ratQuadSub x y) = eval x-eval y := by
  simp only [eval,ratQuadSub,Rat.cast_sub]
  ring

theorem ratQuadMul_eval (x y : RationalQuadratic) : eval (ratQuadMul x y) = eval x*eval y := by
  simp only [eval,ratQuadMul,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem ratQuadHalfInt_eval (x : Quad3) : eval (ratQuadHalfInt x) = Quad3.eval x/2 := by
  simp only [eval,ratQuadHalfInt,Quad3.eval,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
  ring

theorem rational_vertex_eval (i : Fin 14) : rationalPointEval (rationalVertex i) = realVertex i := by
  apply Prod.ext <;> simp only [rationalPointEval,rationalVertex,ratQuadHalfInt_eval,realVertex,realize]

theorem rational_direction_eval (d : Fin 12) : rationalPointEval (rationalDirection d) = realDirection d := by
  apply Prod.ext <;> simp only [rationalPointEval,rationalDirection,ratQuadHalfInt_eval,realDirection,realize]

theorem rational_rotate_eval (k : Fin 12) (p : RationalQuadraticPoint) :
    rationalPointEval (rationalRotate k p) = rotate k (rationalPointEval p) := by
  have h := rational_direction_eval k
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext <;>
    simp only [rationalPointEval,rationalRotate,ratQuadSub_eval,ratQuadAdd_eval,ratQuadMul_eval,
      rotate,complexMulReal] at * <;> rw [h1,h2]

theorem rational_point_eval_injective : Function.Injective rationalPointEval := by
  intro x y h
  apply Prod.ext
  · exact eval_injective (congrArg Prod.fst h)
  · exact eval_injective (congrArg Prod.snd h)

def rationalPointEvalHom : RationalQuadraticPoint →+ RealPoint where
  toFun := rationalPointEval
  map_zero' := by simp [rationalPointEval,eval]
  map_add' := by
    intro p q
    apply Prod.ext <;> simp [rationalPointEval,eval,Rat.cast_add] <;> ring

def quadraticPlane : AddSubgroup RealPoint := rationalPointEvalHom.range

theorem realVertex_mem_quadraticPlane (i : Fin 14) : realVertex i ∈ quadraticPlane :=
  ⟨rationalVertex i,rational_vertex_eval i⟩

theorem rotate_mem_quadraticPlane (k : Fin 12) {p : RealPoint} (hp : p ∈ quadraticPlane) :
    rotate k p ∈ quadraticPlane := by
  obtain ⟨q,hq⟩ := hp
  exact ⟨rationalRotate k q,(rational_rotate_eval k q).trans (congrArg (rotate k) hq)⟩

theorem developPoint_add (p q : RationalQuadraticPoint) : developPoint (p+q) = developPoint p+developPoint q := by
  apply Prod.ext <;> simp only [developPoint,Prod.fst_add,Prod.snd_add] <;> ring

theorem developPoint_sub (p q : RationalQuadraticPoint) : developPoint (p-q) = developPoint p-developPoint q := by
  apply Prod.ext <;> simp only [developPoint,Prod.fst_sub,Prod.snd_sub] <;> ring

end
end SpectreGeometry
