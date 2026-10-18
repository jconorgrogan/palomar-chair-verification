module

public import SpectreGeometry.ReverseAbelianCocycle
public import Mathlib.Tactic.Abel
public import SpectreClusters.ReverseClusterCocycle

@[expose] public section


/-! Matching corner displacements integrate in any additive commutative
group. In particular, checked physical P corner values determine an actual
whole-plane field of physical translations, without a tiling premise. -/
namespace SpectreGeometry.ReverseExistence
open SpectreFinite SpectreFinite.HexSearch SpectreClusters.ReverseExistence

variable {E : Type*} [AddCommGroup E]

def cornerDisplacement (C : State → Fin 6 → E) (a b : State) (d : Fin 6) : E :=
  C a d-C b (rotateTurn 4 d)

def CornerMatching (C : State → Fin 6 → E) : Prop :=
  ∀ a b d, sideMatch a b d → cornerDisplacement C a b d = C a (rotateTurn 1 d)-C b (opposite d)

private theorem turn_four_opposite : ∀ d : Fin 6, rotateTurn 4 (opposite d)=rotateTurn 1 d := by decide
private theorem turn_one_two : ∀ d : Fin 6, rotateTurn 1 (rotateTurn 2 d)=opposite d := by decide
private theorem opposite_two : ∀ d : Fin 6, opposite (rotateTurn 2 d)=rotateTurn 4 (rotateTurn 1 d) := by decide

theorem cornerDisplacement_inverse (C : State → Fin 6 → E) (hC : CornerMatching C)
    (a b : State) (d : Fin 6) (h : sideMatch a b d) :
    cornerDisplacement C a b d+cornerDisplacement C b a (opposite d)=0 := by
  rw [hC a b d h,cornerDisplacement,turn_four_opposite]
  abel

theorem cornerDisplacement_triangle (C : State → Fin 6 → E) (hC : CornerMatching C)
    (a b c : State) (d : Fin 6) (hab : sideMatch a b d)
    (hbc : sideMatch b c (rotateTurn 2 d)) :
    cornerDisplacement C a b d+cornerDisplacement C b c (rotateTurn 2 d)=
      cornerDisplacement C a c (rotateTurn 1 d) := by
  rw [hC a b d hab,hC b c (rotateTurn 2 d) hbc,cornerDisplacement,turn_one_two,opposite_two]
  abel

def cornerFieldDelta (C : State → Fin 6 → E) (f : Position → State) (x : Position) (d : Fin 6) : E :=
  cornerDisplacement C (f x) (f (addPos x (SpectreFinite.direction d))) d

theorem cornerFieldDelta_closed (C : State → Fin 6 → E) (hC : CornerMatching C)
    (f : Position → State) (hf : GloballyLegal f) : AbelianClosedCocycle (cornerFieldDelta C f) := by
  constructor
  · intro x d
    have he : addPos (addPos x (direction d)) (direction (opposite d))=x :=
      positionSystem.opposite_inverse d x
    unfold cornerFieldDelta
    rw [he]
    exact cornerDisplacement_inverse C hC _ _ d (field_sideMatch f hf x d)
  · intro x d
    have he : addPos (addPos x (direction d)) (direction (rotateTurn 2 d)) =
        addPos x (direction (rotateTurn 1 d)) := positionSystem.triangle d x
    have hbc := field_sideMatch f hf (addPos x (direction d)) (rotateTurn 2 d)
    rw [he] at hbc
    unfold cornerFieldDelta
    rw [he]
    exact cornerDisplacement_triangle C hC _ _ _ d (field_sideMatch f hf x d) hbc

/-- The actual globally legal field has the required corner translation
assignment. No injectivity, coverage, or disjointness conclusion is asserted. -/
theorem exists_cornerAnchor (C : State → Fin 6 → E) (hC : CornerMatching C)
    (f : Position → State) (hf : GloballyLegal f) :
    ∃ A : Position → E, A (0,0)=0 ∧ ∀ x d,
      A (addPos x (direction d)) = A x+cornerDisplacement C (f x) (f (addPos x (direction d))) d :=
  exists_abelianIntegratedAnchor (cornerFieldDelta C f) (cornerFieldDelta_closed C hC f hf)

end SpectreGeometry.ReverseExistence
