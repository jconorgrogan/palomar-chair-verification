module

public import SpectreGeometry.PhysicalQuadraticRegistration

@[expose] public section


/-! A single-valued additive development of all registered physical vertices.
This is a map on the rational sqrt(3) point subgroup only; no continuity on
the real plane is claimed. -/
namespace SpectreGeometry
noncomputable section

def quadraticCoordinatesEquiv : RationalQuadraticPoint ≃+ quadraticPlane :=
  AddMonoidHom.ofInjective rational_point_eval_injective

def developPointHom : RationalQuadraticPoint →+ (ℚ × ℚ) where
  toFun := developPoint
  map_zero' := by simp [developPoint]
  map_add' := developPoint_add

def quadraticDevelopment : quadraticPlane →+ (ℚ × ℚ) :=
  developPointHom.comp quadraticCoordinatesEquiv.symm.toAddMonoidHom

theorem quadratic_coordinates_eval (p : quadraticPlane) :
    rationalPointEval (quadraticCoordinatesEquiv.symm p) = p :=
  AddMonoidHom.apply_ofInjective_symm rational_point_eval_injective p

theorem quadraticDevelopment_of_eval (p : RationalQuadraticPoint) :
    quadraticDevelopment ⟨rationalPointEval p, ⟨p,rfl⟩⟩ = developPoint p := by
  change developPoint (quadraticCoordinatesEquiv.symm (quadraticCoordinatesEquiv p)) = _
  rw [quadraticCoordinatesEquiv.symm_apply_apply]

theorem quadraticDevelopment_sum_eval (p : quadraticPlane) (q : RationalQuadraticPoint)
    (h : (p : RealPoint)+rationalPointEval q ∈ quadraticPlane) :
    quadraticDevelopment ⟨(p : RealPoint)+rationalPointEval q,h⟩ =
      quadraticDevelopment p + developPoint q := by
  have he : (⟨(p : RealPoint)+rationalPointEval q,h⟩ : quadraticPlane) =
      p + ⟨rationalPointEval q,⟨q,rfl⟩⟩ := rfl
  rw [he,map_add,quadraticDevelopment_of_eval]

theorem quadraticDevelopment_rotated_vertex (p : quadraticPlane) (k : Fin 12) (e : Fin 14)
    (h : (p : RealPoint)+rotate k (realVertex e) ∈ quadraticPlane) :
    quadraticDevelopment ⟨(p : RealPoint)+rotate k (realVertex e),h⟩ =
      quadraticDevelopment p + rationalKitePoint (deformedVertex k e) := by
  have hq : rationalPointEval (rationalRotate k (rationalVertex e)) = rotate k (realVertex e) := by
    rw [rational_rotate_eval,rational_vertex_eval]
  have hh := quadraticDevelopment_sum_eval p (rationalRotate k (rationalVertex e))
    (by rwa [hq])
  simpa only [hq,developed_rotated_vertices] using hh

/-- The globally defined point map agrees on every physical tile's vertices
with its literal parity-developed polygon, translated by one origin. -/
theorem physical_vertex_development_formula (root f : EPlane ≃ᵢ EPlane) (k : Fin 12)
    (hframe : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate k q))
    (horigin : sourcePoint root (f 0) ∈ quadraticPlane) (e : Fin 14) :
    quadraticDevelopment ⟨sourcePoint root (f (euclideanVertex e)),
      relative_vertex_mem_quadraticPlane root f k hframe horigin e⟩ =
    quadraticDevelopment ⟨sourcePoint root (f 0),horigin⟩ + rationalKitePoint (deformedVertex k e) := by
  have hp := relative_sourcePoint root f k hframe (realVertex e)
  have hh := quadraticDevelopment_rotated_vertex ⟨sourcePoint root (f 0),horigin⟩ k e
    (quadraticPlane.add_mem horigin (rotate_mem_quadraticPlane k (realVertex_mem_quadraticPlane e)))
  simpa only [←hp,euclideanVertex] using hh

theorem shared_physical_vertex_development (root f g : EPlane ≃ᵢ EPlane)
    (a b : Fin 12)
    (ha : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate a q))
    (hb : ∀ q : RealPoint, coordinateAction g q = coordinateAction root (rotate b q))
    (hf : sourcePoint root (f 0) ∈ quadraticPlane)
    (hg : sourcePoint root (g 0) ∈ quadraticPlane) (e j : Fin 14)
    (he : f (euclideanVertex e) = g (euclideanVertex j)) :
    quadraticDevelopment ⟨sourcePoint root (f 0),hf⟩ + rationalKitePoint (deformedVertex a e) =
    quadraticDevelopment ⟨sourcePoint root (g 0),hg⟩ + rationalKitePoint (deformedVertex b j) := by
  rw [←physical_vertex_development_formula root f a ha hf e,
    ←physical_vertex_development_formula root g b hb hg j]
  congr 1
  exact Subtype.ext (congrArg (sourcePoint root) he)

end
end SpectreGeometry
