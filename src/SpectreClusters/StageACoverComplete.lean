module

public import SpectreClusters.StageACoverAPart4
public import SpectreClusters.StageACoverBPart5

@[expose] public section


/-! Exhaustion theorem for the literal index tables. Geometric binding is
provided separately; this declaration alone is not physical completeness. -/
namespace SpectreClusters.StageA
open FiniteCoverWords

theorem coverTable_complete (kind : HTKind) :
    enumerate (idCompatible kind) (choicesTable kind) = rawWords kind := by
  cases kind with
  | hat => exact suffixA19_complete
  | turtle => exact suffixB21_complete

theorem mem_rawWords_iff (kind : HTKind) (word : List Nat) :
    word ∈ rawWords kind ↔ OverChoices word (choicesTable kind) ∧
      word.Pairwise (fun a b => idCompatible kind a b = true) := by
  rw [← coverTable_complete]
  exact mem_enumerate_iff _ _ _

set_option maxRecDepth 100000 in
theorem rawWords_count (kind : HTKind) : (rawWords kind).length = 251 := by
  cases kind <;> rfl

end SpectreClusters.StageA
