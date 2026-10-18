module

public import SpectreClusters.StageAActualSupport

@[expose] public section


/-! Exact radius-two cover witnesses for all regular final hat rows. -/
namespace SpectreClusters.StageA

set_option maxRecDepth 100000

def hasDirectTurtleCoverB (i : Nat) : Bool :=
  (rawWordAt .hat i).any fun n =>
    ((candidateAt .hat n).kind == .turtle) &&
      (clusterPiecesAt .t8h (candidateAt .hat n)).contains (canonicalRoot .hat)

theorem regular_hat_cover_check :
    (keptIds 2 .hat).all (fun i => i == 210 || hasDirectTurtleCoverB i ||
      [16,27,38].contains i) = true := by rfl

theorem regular_hat_cover_alternatives (i : Nat) (hi : i ∈ keptIds 2 .hat)
    (hne : i ≠ 210) :
    (∃ n ∈ rawWordAt .hat i, (candidateAt .hat n).kind = .turtle ∧
      canonicalRoot .hat ∈ clusterPiecesAt .t8h (candidateAt .hat n)) ∨
    i = 16 ∨ i = 27 ∨ i = 38 := by
  have h := List.all_eq_true.mp regular_hat_cover_check i hi
  simpa [hne,hasDirectTurtleCoverB,List.any_eq_true] using h

theorem hat16_up_mem : 2 ∈ rawWordAt .hat 16 := by decide
theorem hat27_up_mem : 2 ∈ rawWordAt .hat 27 := by decide
theorem hat38_up_mem : 2 ∈ rawWordAt .hat 38 := by decide
theorem hat_up_alignment : alignmentValidB .hat 2 = true := by rfl

def upSupportCheckB (i : Nat) : Bool :=
  (keptIds 2 .hat).all fun j =>
    !(supportB .hat (rawWordAt .hat i) 2 (rawWordAt .hat j)) || [8,15].contains j

theorem hat16_up_support_check : upSupportCheckB 16 = true := by rfl
theorem hat27_up_support_check : upSupportCheckB 27 = true := by rfl
theorem hat38_up_support_check : upSupportCheckB 38 = true := by rfl

theorem up_support_of_check (i j : Nat) (hc : upSupportCheckB i = true)
    (hj : j ∈ keptIds 2 .hat)
    (hs : supportB .hat (rawWordAt .hat i) 2 (rawWordAt .hat j) = true) :
    j = 8 ∨ j = 15 := by
  have h := List.all_eq_true.mp hc j hj
  simpa [hs] using h

theorem up_row8_turtle_mem : 33 ∈ rawWordAt .hat 8 := by decide
theorem up_row15_turtle_mem : 51 ∈ rawWordAt .hat 15 := by decide

def firstUpperTurtle : HTPlacement :=
  movePlacement (candidateAt .hat 2).turn (candidateAt .hat 2).center (candidateAt .hat 33)
def secondUpperTurtle : HTPlacement :=
  movePlacement (candidateAt .hat 2).turn (candidateAt .hat 2).center (candidateAt .hat 51)

theorem firstUpperTurtle_kind : firstUpperTurtle.kind = .turtle := rfl
theorem secondUpperTurtle_kind : secondUpperTurtle.kind = .turtle := rfl

theorem firstUpperTurtle_covers :
    canonicalRoot .hat ∈ clusterPiecesAt .t8h firstUpperTurtle := by decide
theorem secondUpperTurtle_covers :
    canonicalRoot .hat ∈ clusterPiecesAt .t8h secondUpperTurtle := by decide

end SpectreClusters.StageA
