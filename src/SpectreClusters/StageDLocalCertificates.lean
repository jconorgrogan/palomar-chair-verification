module

public import SpectreClusters.StageDFinalChecksModel

@[expose] public section


/-! Exact finite law obligations, separated from actual-occurrence soundness
so the generic proof can be checked before the finite table replay finishes. -/
namespace SpectreClusters.StageD

structure FinalRowChecks : Prop where
  pairs : ∀ (i : Row) (d : Fin 6) (j : Row), pairCheckB i d j = true
  unique : ∀ i j : Row, uniqueCheckB i j = true
  basics : ∀ i : Row, rowBasicsB i = true

end SpectreClusters.StageD
