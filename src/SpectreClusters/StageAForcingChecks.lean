module

public import SpectreClusters.StageALocalClaims

@[expose] public section


/-! Small literal consequences of the final23-row family. These finite checks
are used only after actual-field membership in that family has been proved. -/
namespace SpectreClusters.StageA

set_option maxRecDepth 100000

theorem turtle_core_hat_alignment : alignmentValidB .turtle 3 = true := by rfl

theorem turtle_core_hat_support_check :
    (keptIds 2 .hat).all (fun j =>
      !(supportB .turtle (rawWordAt .turtle 0) 3 (rawWordAt .hat j)) ||
        [6,8].contains j) = true := by rfl

theorem turtle_core_hat_support (j : Nat) (hj : j ∈ keptIds 2 .hat)
    (hs : supportB .turtle (rawWordAt .turtle 0) 3 (rawWordAt .hat j) = true) :
    j = 6 ∨ j = 8 := by
  have h := List.all_eq_true.mp turtle_core_hat_support_check j hj
  simpa [hs] using h

end SpectreClusters.StageA
