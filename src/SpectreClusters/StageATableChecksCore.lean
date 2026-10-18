module

public import SpectreClusters.StageABindingCore

@[expose] public section

namespace SpectreClusters.StageA

def compatibilityRowB (kind : HTKind) (i : Nat) : Bool :=
  (List.range (candidateList kind).length).all fun j =>
    idCompatible kind i j == compatibleB (candidateAt kind i) (candidateAt kind j)

theorem compatibilityRow_sound (kind : HTKind) (i : Nat)
    (h : compatibilityRowB kind i = true) (j : Nat)
    (hj : j < (candidateList kind).length) :
    idCompatible kind i j = compatibleB (candidateAt kind i) (candidateAt kind j) := by
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  exact beq_iff_eq.mp this

end SpectreClusters.StageA
