module

public import SpectreFinite.HexStepAction
public import SpectreClusters.KiteGrid

@[expose] public section


/-! Integrating an actual closed axial displacement cocycle. This produces
all-plane anchor coordinates from inverse/triangle laws; injectivity, coverage,
and physical tile realization are deliberately separate conclusions. -/
namespace SpectreClusters.ReverseExistence
open SpectreFinite SpectreFinite.HexSearch

set_option backward.privateInPublic true in
theorem position_cancel (x : Position) (d : Fin 6) :
    addPos (addPos x (direction d)) (direction (opposite d)) = x := by
  rw [direction_opposite]
  apply Prod.ext <;> simp [addPos] <;> omega

private theorem direction_triangle : ∀ d : Fin 6,
    addPos (direction d) (direction (rotateTurn 2 d)) = direction (rotateTurn 1 d) := by decide

set_option backward.privateInPublic true in
theorem position_triangle (x : Position) (d : Fin 6) :
    addPos (addPos x (direction d)) (direction (rotateTurn 2 d)) =
      addPos x (direction (rotateTurn 1 d)) := by
  have h := direction_triangle d
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> simp [addPos] at * <;> omega

structure ClosedCocycle (D : Position → Fin 6 → Point) : Prop where
  inverse : ∀ x d, add (D x d) (D (addPos x (direction d)) (opposite d)) = (0,0)
  triangle : ∀ x d, add (D x d) (D (addPos x (direction d)) (rotateTurn 2 d)) =
    D x (rotateTurn 1 d)

set_option backward.privateInPublic true in
def liftedSystem (D : Position → Fin 6 → Point) (hD : ClosedCocycle D) :
    HexStepSystem (Position × Point) where
  step d z := (addPos z.1 (direction d),add z.2 (D z.1 d))
  opposite_inverse d z := by
    apply Prod.ext
    · exact position_cancel z.1 d
    · have h := hD.inverse z.1 d
      have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      apply Prod.ext <;> simp [add] at * <;> omega
  triangle d z := by
    apply Prod.ext
    · exact position_triangle z.1 d
    · have h := hD.triangle z.1 d
      have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      apply Prod.ext <;> simp [add] at * <;> omega

set_option backward.privateInPublic true in
def positionSystem : HexStepSystem Position where
  step d x := addPos x (direction d)
  opposite_inverse := fun d x => position_cancel x d
  triangle := fun d x => position_triangle x d

private theorem position_iterate0 (n : Nat) (x : Position) :
    ReversibleStep.iterate (positionSystem.step 0) n x = (x.1-n,x.2) := by
  induction n with
  | zero => simp [ReversibleStep.iterate]
  | succ n ih =>
      rw [ReversibleStep.iterate,ih]
      change (x.1-(n : Int)+(-1),x.2+0) = (x.1-(n+1 : Nat),x.2)
      apply Prod.ext <;> simp <;> omega

private theorem position_iterate3 (n : Nat) (x : Position) :
    ReversibleStep.iterate (positionSystem.step 3) n x = (x.1+n,x.2) := by
  induction n with
  | zero => simp [ReversibleStep.iterate]
  | succ n ih =>
      rw [ReversibleStep.iterate,ih]
      change (x.1+(n : Int)+1,x.2+0) = (x.1+(n+1 : Nat),x.2)
      apply Prod.ext <;> simp <;> omega

private theorem position_iterate2 (n : Nat) (x : Position) :
    ReversibleStep.iterate (positionSystem.step 2) n x = (x.1+n,x.2-n) := by
  induction n with
  | zero => simp [ReversibleStep.iterate]
  | succ n ih =>
      rw [ReversibleStep.iterate,ih]
      change (x.1+(n : Int)+1,x.2-(n : Int)+(-1)) = (x.1+(n+1 : Nat),x.2-(n+1 : Nat))
      apply Prod.ext <;> simp <;> omega

private theorem position_iterate5 (n : Nat) (x : Position) :
    ReversibleStep.iterate (positionSystem.step 5) n x = (x.1-n,x.2+n) := by
  induction n with
  | zero => simp [ReversibleStep.iterate]
  | succ n ih =>
      rw [ReversibleStep.iterate,ih]
      change (x.1-(n : Int)+(-1),x.2+(n : Int)+1) = (x.1-(n+1 : Nat),x.2+(n+1 : Nat))
      apply Prod.ext <;> simp <;> omega

private theorem position_axis0 (n : Int) (x : Position) :
    positionSystem.axis0.act n x = (x.1-n,x.2) := by
  cases n with
  | ofNat n => exact position_iterate0 n x
  | negSucc n =>
      change ReversibleStep.iterate (positionSystem.step 3) (n+1) x = _
      rw [position_iterate3]
      apply Prod.ext <;> simp <;> omega

private theorem position_axis2 (n : Int) (x : Position) :
    positionSystem.axis2.act n x = (x.1+n,x.2-n) := by
  cases n with
  | ofNat n => exact position_iterate2 n x
  | negSucc n =>
      change ReversibleStep.iterate (positionSystem.step 5) (n+1) x = _
      rw [position_iterate5]
      apply Prod.ext <;> simp <;> omega

theorem position_translate (v x : Position) : positionSystem.translate v x = addPos v x := by
  rw [HexStepSystem.translate,position_axis2,position_axis0]
  apply Prod.ext <;> simp [addPos] <;> omega

theorem lifted_translate_position (D : Position → Fin 6 → Point) (hD : ClosedCocycle D)
    (v : Position) (z : Position × Point) :
    ((liftedSystem D hD).translate v z).1 = addPos v z.1 := by
  have h := (liftedSystem D hD).map_translate positionSystem Prod.fst (fun _ _ => rfl) v z
  exact h.trans (position_translate v z.1)

/-- The exact path-integral anchor, constructed by the proved lattice action. -/
def integratedAnchor (D : Position → Fin 6 → Point) (hD : ClosedCocycle D) (x : Position) : Point :=
  ((liftedSystem D hD).translate x ((0,0),(0,0))).2

@[simp] theorem integratedAnchor_zero (D : Position → Fin 6 → Point) (hD : ClosedCocycle D) :
    integratedAnchor D hD (0,0) = (0,0) := rfl

theorem integratedAnchor_step (D : Position → Fin 6 → Point) (hD : ClosedCocycle D)
    (x : Position) (d : Fin 6) :
    integratedAnchor D hD (addPos x (direction d)) = add (integratedAnchor D hD x) (D x d) := by
  have hc : addPos x (direction d) = addPos (direction d) x := by
    apply Prod.ext <;> simp [addPos,Int.add_comm]
  unfold integratedAnchor
  rw [hc,HexStepSystem.translate_add,HexStepSystem.translate_direction]
  change add _ (D (((liftedSystem D hD).translate x ((0,0),(0,0))).1) d) = _
  rw [lifted_translate_position]
  simp [addPos]

/-- Closed local data gives a global anchor assignment with every prescribed
neighbor displacement, without a geometric realization hypothesis. -/
theorem exists_integratedAnchor (D : Position → Fin 6 → Point) (hD : ClosedCocycle D) :
    ∃ A : Position → Point, A (0,0) = (0,0) ∧
      ∀ x d, A (addPos x (direction d)) = add (A x) (D x d) :=
  ⟨integratedAnchor D hD,integratedAnchor_zero D hD,integratedAnchor_step D hD⟩

end SpectreClusters.ReverseExistence
