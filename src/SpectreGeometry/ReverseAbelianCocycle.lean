module

public import SpectreClusters.ReverseClusterCocycleIntegration
public import Mathlib.Algebra.Group.Defs

@[expose] public section


/-! The exact hexagonal path integration also works in any additive
commutative group, including physical real translation vectors. -/
namespace SpectreGeometry.ReverseExistence
open SpectreFinite SpectreFinite.HexSearch
open SpectreClusters.ReverseExistence

variable {E : Type*} [AddCommGroup E]

structure AbelianClosedCocycle (D : Position → Fin 6 → E) : Prop where
  inverse : ∀ x d, D x d + D (addPos x (direction d)) (opposite d) = 0
  triangle : ∀ x d, D x d + D (addPos x (direction d)) (rotateTurn 2 d) = D x (rotateTurn 1 d)

def abelianLiftedSystem (D : Position → Fin 6 → E) (hD : AbelianClosedCocycle D) :
    HexStepSystem (Position × E) where
  step d z := (addPos z.1 (direction d),z.2+D z.1 d)
  opposite_inverse d z := by
    apply Prod.ext
    · exact positionSystem.opposite_inverse d z.1
    · exact (add_assoc _ _ _).trans (by rw [hD.inverse,add_zero])
  triangle d z := by
    apply Prod.ext
    · exact positionSystem.triangle d z.1
    · exact (add_assoc _ _ _).trans (by rw [hD.triangle])

theorem abelianLifted_translate_position (D : Position → Fin 6 → E) (hD : AbelianClosedCocycle D)
    (v : Position) (z : Position × E) :
    ((abelianLiftedSystem D hD).translate v z).1 = addPos v z.1 := by
  have h := (abelianLiftedSystem D hD).map_translate positionSystem Prod.fst (fun _ _ => rfl) v z
  exact h.trans (position_translate v z.1)

def abelianIntegratedAnchor (D : Position → Fin 6 → E) (hD : AbelianClosedCocycle D)
    (x : Position) : E := ((abelianLiftedSystem D hD).translate x ((0,0),0)).2

@[simp] theorem abelianIntegratedAnchor_zero (D : Position → Fin 6 → E)
    (hD : AbelianClosedCocycle D) : abelianIntegratedAnchor D hD (0,0) = 0 := rfl

theorem abelianIntegratedAnchor_step (D : Position → Fin 6 → E) (hD : AbelianClosedCocycle D)
    (x : Position) (d : Fin 6) :
    abelianIntegratedAnchor D hD (addPos x (direction d)) = abelianIntegratedAnchor D hD x+D x d := by
  have hc : addPos x (direction d) = addPos (direction d) x := by
    apply Prod.ext <;> simp [addPos,Int.add_comm]
  unfold abelianIntegratedAnchor
  rw [hc,HexStepSystem.translate_add,HexStepSystem.translate_direction]
  change _ + D (((abelianLiftedSystem D hD).translate x ((0,0),0)).1) d = _
  rw [abelianLifted_translate_position]
  simp [addPos]

theorem exists_abelianIntegratedAnchor (D : Position → Fin 6 → E) (hD : AbelianClosedCocycle D) :
    ∃ A : Position → E, A (0,0)=0 ∧ ∀ x d, A (addPos x (direction d))=A x+D x d :=
  ⟨abelianIntegratedAnchor D hD,abelianIntegratedAnchor_zero D hD,abelianIntegratedAnchor_step D hD⟩

end SpectreGeometry.ReverseExistence
