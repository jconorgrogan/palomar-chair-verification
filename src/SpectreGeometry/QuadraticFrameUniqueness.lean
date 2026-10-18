module

public import SpectreGeometry.QuadraticPointReal
public import SpectreGeometry.CyclicFrameRegistration

@[expose] public section


namespace SpectreGeometry
noncomputable section

theorem rationalDirection_injective : Function.Injective rationalDirection := by
  exact (by decide +kernel : ∀ i j : Fin 12, rationalDirection i = rationalDirection j → i = j)

theorem realDirection_injective : Function.Injective realDirection := by
  intro i j h
  apply rationalDirection_injective
  apply rational_point_eval_injective
  simpa only [rational_direction_eval] using h

theorem rotate_first_vector (k : Fin 12) : rotate k (1,0) = realDirection k := by
  apply Prod.ext <;> simp [rotate,complexMulReal]

theorem relative_frame_unique (root f : EPlane ≃ᵢ EPlane) (a b : Fin 12)
    (ha : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate a q))
    (hb : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate b q)) : a = b := by
  apply realDirection_injective
  apply (coordinateAction root).injective
  have hh := (ha (1,0)).symm.trans (hb (1,0))
  simpa only [rotate_first_vector] using hh

theorem relative_frames_compose (root f g : EPlane ≃ᵢ EPlane) (a b k : Fin 12)
    (ha : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate a q))
    (hb : ∀ q : RealPoint, coordinateAction g q = coordinateAction root (rotate b q))
    (hk : ∀ q : RealPoint, coordinateAction g q = coordinateAction f (rotate k q)) :
    b = directionAdd a k := by
  apply relative_frame_unique root g b (directionAdd a k) hb
  intro q
  rw [hk,ha,rotate_add]

end
end SpectreGeometry
