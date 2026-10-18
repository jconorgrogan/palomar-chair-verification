module

public import SpectreFinite.HexRotationComposition
public import SpectreFinite.IntegerStepAction

@[expose] public section


/-! The two local hexagonal step laws imply an action of the additive axial
integer lattice. The action need not be free or transitive. -/
namespace SpectreFinite.HexSearch

structure HexStepSystem (X : Type u) where
  step : Fin 6 → X → X
  opposite_inverse : ∀ d x, step (opposite d) (step d x) = x
  triangle : ∀ d x, step (rotateTurn 2 d) (step d x) = step (rotateTurn 1 d) x

namespace HexStepSystem

variable (S : HexStepSystem X)

def axis0 : ReversibleStep X where
  forward := S.step 0
  backward := S.step 3
  backward_forward := S.opposite_inverse 0
  forward_backward := S.opposite_inverse 3

def axis2 : ReversibleStep X where
  forward := S.step 2
  backward := S.step 5
  backward_forward := S.opposite_inverse 2
  forward_backward := S.opposite_inverse 5

theorem step0_step2 (x : X) : S.step 0 (S.step 2 x) = S.step 1 x := by
  have ht : S.step 3 (S.step 1 x) = S.step 2 x := S.triangle 1 x
  have hi : S.step 0 (S.step 3 (S.step 1 x)) = S.step 1 x :=
    S.opposite_inverse 3 (S.step 1 x)
  rw [ht] at hi
  exact hi

theorem basis_commute (x : X) :
    S.axis0.forward (S.axis2.forward x) = S.axis2.forward (S.axis0.forward x) := by
  exact (S.step0_step2 x).trans (S.triangle 0 x).symm

theorem step3_step5 (x : X) : S.step 3 (S.step 5 x) = S.step 4 x := by
  have ht : S.step 0 (S.step 4 x) = S.step 5 x := S.triangle 4 x
  have hi : S.step 3 (S.step 0 (S.step 4 x)) = S.step 4 x :=
    S.opposite_inverse 0 (S.step 4 x)
  rw [ht] at hi
  exact hi

/-- Canonical axial translation, using the W and SE steps as a basis. -/
def translate (v : Position) (x : X) : X :=
  S.axis0.act (-v.1-v.2) (S.axis2.act (-v.2) x)

@[simp] theorem translate_zero (x : X) : S.translate (0,0) x = x := rfl

theorem translate_add (u v : Position) (x : X) :
    S.translate (addPos u v) x = S.translate u (S.translate v x) := by
  dsimp only [translate, addPos]
  have ha : -(u.1+v.1)-(u.2+v.2) = (-u.1-u.2)+(-v.1-v.2) := by omega
  have hb : -(u.2+v.2) = -u.2 + -v.2 := by omega
  rw [ha, hb, ReversibleStep.act_add, ReversibleStep.act_add]
  rw [S.axis0.act_commute S.axis2 S.basis_commute (-v.1-v.2) (-u.2)]

private theorem six_cases {P : Fin 6 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5) :
    ∀ t, P t :=
  Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3
    (Fin.cases h4 (Fin.cases h5 (fun t => Fin.elim0 t))))))

theorem translate_direction : ∀ d : Fin 6, ∀ x : X,
    S.translate (direction d) x = S.step d x := by
  apply six_cases
  · intro x; rfl
  · intro x; exact S.step0_step2 x
  · intro x; rfl
  · intro x; rfl
  · intro x; exact S.step3_step5 x
  · intro x; rfl

/-- A map intertwining the six steps intertwines every axial translation. -/
theorem map_translate (T : HexStepSystem Y) (f : X → Y)
    (hf : ∀ d x, f (S.step d x) = T.step d (f x)) (v : Position) (x : X) :
    f (S.translate v x) = T.translate v (f x) := by
  unfold translate
  rw [S.axis0.map_act T.axis0 f (hf 0), S.axis2.map_act T.axis2 f (hf 2)]

end HexStepSystem
end SpectreFinite.HexSearch
