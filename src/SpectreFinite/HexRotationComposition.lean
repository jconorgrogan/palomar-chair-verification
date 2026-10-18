module

public import SpectreFinite.HexRotation

@[expose] public section


/-! Exact composition laws for the discrete sixfold rotations. -/
namespace SpectreFinite.HexSearch

private theorem six_cases {P : Fin 6 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) :
    ∀ t, P t :=
  Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3
    (Fin.cases h4 (Fin.cases h5 (fun t => Fin.elim0 t))))))

theorem rotateTurn_assoc : ∀ t s r : Fin 6,
    rotateTurn t (rotateTurn s r) = rotateTurn (rotateTurn t s) r := by decide

theorem rotateTurn_comm : ∀ t s : Fin 6, rotateTurn t s = rotateTurn s t := by decide

theorem rotatePosition_comp : ∀ t s : Fin 6, ∀ x : Position,
    rotatePosition t (rotatePosition s x) = rotatePosition (rotateTurn t s) x := by
  apply six_cases
  · apply six_cases
    · intro x
      change (x.1, x.2) = (x.1, x.2)
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(x.2), (x.1)+(x.2)) = (-(x.2), (x.1)+(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(x.1)-(x.2), x.1) = (-(x.1)-(x.2), x.1)
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(x.1), -(x.2)) = (-(x.1), -(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (x.2, -(x.1)-(x.2)) = (x.2, -(x.1)-(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change ((x.1)+(x.2), -(x.1)) = ((x.1)+(x.2), -(x.1))
      apply Prod.ext <;> dsimp <;> omega
  · apply six_cases
    · intro x
      change (-(x.2), (x.1)+(x.2)) = (-(x.2), (x.1)+(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-((x.1)+(x.2)), (-(x.2))+((x.1)+(x.2))) = (-(x.1)-(x.2), x.1)
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(x.1), (-(x.1)-(x.2))+(x.1)) = (-(x.1), -(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(-(x.2)), (-(x.1))+(-(x.2))) = (x.2, -(x.1)-(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(-(x.1)-(x.2)), (x.2)+(-(x.1)-(x.2))) = ((x.1)+(x.2), -(x.1))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(-(x.1)), ((x.1)+(x.2))+(-(x.1))) = (x.1, x.2)
      apply Prod.ext <;> dsimp <;> omega
  · apply six_cases
    · intro x
      change (-(x.1)-(x.2), x.1) = (-(x.1)-(x.2), x.1)
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(-(x.2))-((x.1)+(x.2)), -(x.2)) = (-(x.1), -(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(-(x.1)-(x.2))-(x.1), -(x.1)-(x.2)) = (x.2, -(x.1)-(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(-(x.1))-(-(x.2)), -(x.1)) = ((x.1)+(x.2), -(x.1))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(x.2)-(-(x.1)-(x.2)), x.2) = (x.1, x.2)
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-((x.1)+(x.2))-(-(x.1)), (x.1)+(x.2)) = (-(x.2), (x.1)+(x.2))
      apply Prod.ext <;> dsimp <;> omega
  · apply six_cases
    · intro x
      change (-(x.1), -(x.2)) = (-(x.1), -(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(-(x.2)), -((x.1)+(x.2))) = (x.2, -(x.1)-(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(-(x.1)-(x.2)), -(x.1)) = ((x.1)+(x.2), -(x.1))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(-(x.1)), -(-(x.2))) = (x.1, x.2)
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(x.2), -(-(x.1)-(x.2))) = (-(x.2), (x.1)+(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-((x.1)+(x.2)), -(-(x.1))) = (-(x.1)-(x.2), x.1)
      apply Prod.ext <;> dsimp <;> omega
  · apply six_cases
    · intro x
      change (x.2, -(x.1)-(x.2)) = (x.2, -(x.1)-(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change ((x.1)+(x.2), -(-(x.2))-((x.1)+(x.2))) = ((x.1)+(x.2), -(x.1))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (x.1, -(-(x.1)-(x.2))-(x.1)) = (x.1, x.2)
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(x.2), -(-(x.1))-(-(x.2))) = (-(x.2), (x.1)+(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(x.1)-(x.2), -(x.2)-(-(x.1)-(x.2))) = (-(x.1)-(x.2), x.1)
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (-(x.1), -((x.1)+(x.2))-(-(x.1))) = (-(x.1), -(x.2))
      apply Prod.ext <;> dsimp <;> omega
  · apply six_cases
    · intro x
      change ((x.1)+(x.2), -(x.1)) = ((x.1)+(x.2), -(x.1))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change ((-(x.2))+((x.1)+(x.2)), -(-(x.2))) = (x.1, x.2)
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change ((-(x.1)-(x.2))+(x.1), -(-(x.1)-(x.2))) = (-(x.2), (x.1)+(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change ((-(x.1))+(-(x.2)), -(-(x.1))) = (-(x.1)-(x.2), x.1)
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change ((x.2)+(-(x.1)-(x.2)), -(x.2)) = (-(x.1), -(x.2))
      apply Prod.ext <;> dsimp <;> omega
    · intro x
      change (((x.1)+(x.2))+(-(x.1)), -((x.1)+(x.2))) = (x.2, -(x.1)-(x.2))
      apply Prod.ext <;> dsimp <;> omega

theorem rotatedField_apply_rotated (t : Fin 6) (f : Position → State) (x : Position) :
    rotatedField t f (rotatePosition t x) = rotateState t (f x) := by
  simp only [rotatedField, rotatePosition_inverse]

theorem rotateState_comp (t s : Fin 6) (a : State) :
    rotateState t (rotateState s a) = rotateState (rotateTurn t s) a := by
  apply Prod.ext
  · rfl
  · exact rotateTurn_assoc t s a.2

end SpectreFinite.HexSearch
