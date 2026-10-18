module

public import SpectreFinite.HexStepAction

@[expose] public section


/-! A labelled total hex-step system gives a genuinely globally legal axial
field by pullback. Freeness, transitivity and geometric embedding are not
needed for this existence bridge. A total system must still be constructed. -/
namespace SpectreFinite.HexSearch

def HexStepSystem.labelField (S : HexStepSystem X) (label : X → State) (root : X) :
    Position → State := fun x => label (S.translate x root)

theorem HexStepSystem.labelField_globallyLegal (S : HexStepSystem X) (label : X → State)
    (hm : ∀ (d : Fin 6) (a : X),
      facingMark (placed ((0,0),label a)) d =
        -facingMark (placed ((0,0),label (S.step d a))) (opposite d)) (root : X) :
    GloballyLegal (S.labelField label root) := by
  intro x y hxy
  change x ≠ y ∧ _
  refine ⟨hxy,?_⟩
  intro d hd
  change y = addPos x (direction d) at hd
  subst y
  have hc : addPos x (direction d) = addPos (direction d) x := by
    apply Prod.ext <;> simp only [addPos] <;> omega
  change facingMark (placed ((0,0),label (S.translate x root))) d =
    -facingMark (placed ((0,0),label (S.translate (addPos x (direction d)) root))) (opposite d)
  rw [hc,S.translate_add,S.translate_direction]
  exact hm d (S.translate x root)

end SpectreFinite.HexSearch
