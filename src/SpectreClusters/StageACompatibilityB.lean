module

public import SpectreClusters.StageACompatibilityBPart0
public import SpectreClusters.StageACompatibilityBPart1
public import SpectreClusters.StageACompatibilityBPart2
public import SpectreClusters.StageACompatibilityBPart3
public import SpectreClusters.StageACompatibilityBPart4
public import SpectreClusters.StageACompatibilityBPart5
public import SpectreClusters.StageACompatibilityBPart6
public import SpectreClusters.StageACompatibilityBPart7
public import SpectreClusters.StageACompatibilityBPart8
public import SpectreClusters.StageACompatibilityBPart9
public import SpectreClusters.StageACompatibilityBPart10
public import SpectreClusters.StageACompatibilityBPart11
public import SpectreClusters.StageACompatibilityBPart12
public import SpectreClusters.StageACompatibilityBPart13
public import SpectreClusters.StageACompatibilityBPart14
public import SpectreClusters.StageACompatibilityBPart15

@[expose] public section

namespace SpectreClusters.StageA

set_option maxRecDepth 100000
theorem compatibilityB_all : (List.range 64).all (compatibilityRowB .turtle) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hn := List.mem_range.mp hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact compatibilityB_row0
  · exact compatibilityB_row1
  · exact compatibilityB_row2
  · exact compatibilityB_row3
  · exact compatibilityB_row4
  · exact compatibilityB_row5
  · exact compatibilityB_row6
  · exact compatibilityB_row7
  · exact compatibilityB_row8
  · exact compatibilityB_row9
  · exact compatibilityB_row10
  · exact compatibilityB_row11
  · exact compatibilityB_row12
  · exact compatibilityB_row13
  · exact compatibilityB_row14
  · exact compatibilityB_row15
  · exact compatibilityB_row16
  · exact compatibilityB_row17
  · exact compatibilityB_row18
  · exact compatibilityB_row19
  · exact compatibilityB_row20
  · exact compatibilityB_row21
  · exact compatibilityB_row22
  · exact compatibilityB_row23
  · exact compatibilityB_row24
  · exact compatibilityB_row25
  · exact compatibilityB_row26
  · exact compatibilityB_row27
  · exact compatibilityB_row28
  · exact compatibilityB_row29
  · exact compatibilityB_row30
  · exact compatibilityB_row31
  · exact compatibilityB_row32
  · exact compatibilityB_row33
  · exact compatibilityB_row34
  · exact compatibilityB_row35
  · exact compatibilityB_row36
  · exact compatibilityB_row37
  · exact compatibilityB_row38
  · exact compatibilityB_row39
  · exact compatibilityB_row40
  · exact compatibilityB_row41
  · exact compatibilityB_row42
  · exact compatibilityB_row43
  · exact compatibilityB_row44
  · exact compatibilityB_row45
  · exact compatibilityB_row46
  · exact compatibilityB_row47
  · exact compatibilityB_row48
  · exact compatibilityB_row49
  · exact compatibilityB_row50
  · exact compatibilityB_row51
  · exact compatibilityB_row52
  · exact compatibilityB_row53
  · exact compatibilityB_row54
  · exact compatibilityB_row55
  · exact compatibilityB_row56
  · exact compatibilityB_row57
  · exact compatibilityB_row58
  · exact compatibilityB_row59
  · exact compatibilityB_row60
  · exact compatibilityB_row61
  · exact compatibilityB_row62
  · exact compatibilityB_row63

theorem compatibilityB_bound (i j : Nat) (hi : i < 64) (hj : j < 64) :
    idCompatible .turtle i j = compatibleB (candidateAt .turtle i) (candidateAt .turtle j) := by
  exact compatibilityRow_sound .turtle i (List.all_eq_true.mp compatibilityB_all i (List.mem_range.mpr hi)) j hj
end SpectreClusters.StageA
