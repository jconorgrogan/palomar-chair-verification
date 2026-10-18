module

public import SpectreClusters.StageACompatibilityAPart0
public import SpectreClusters.StageACompatibilityAPart1
public import SpectreClusters.StageACompatibilityAPart2
public import SpectreClusters.StageACompatibilityAPart3
public import SpectreClusters.StageACompatibilityAPart4
public import SpectreClusters.StageACompatibilityAPart5
public import SpectreClusters.StageACompatibilityAPart6
public import SpectreClusters.StageACompatibilityAPart7
public import SpectreClusters.StageACompatibilityAPart8
public import SpectreClusters.StageACompatibilityAPart9
public import SpectreClusters.StageACompatibilityAPart10
public import SpectreClusters.StageACompatibilityAPart11
public import SpectreClusters.StageACompatibilityAPart12
public import SpectreClusters.StageACompatibilityAPart13
public import SpectreClusters.StageACompatibilityAPart14

@[expose] public section

namespace SpectreClusters.StageA

set_option maxRecDepth 100000
theorem compatibilityA_all : (List.range 59).all (compatibilityRowB .hat) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hn := List.mem_range.mp hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact compatibilityA_row0
  · exact compatibilityA_row1
  · exact compatibilityA_row2
  · exact compatibilityA_row3
  · exact compatibilityA_row4
  · exact compatibilityA_row5
  · exact compatibilityA_row6
  · exact compatibilityA_row7
  · exact compatibilityA_row8
  · exact compatibilityA_row9
  · exact compatibilityA_row10
  · exact compatibilityA_row11
  · exact compatibilityA_row12
  · exact compatibilityA_row13
  · exact compatibilityA_row14
  · exact compatibilityA_row15
  · exact compatibilityA_row16
  · exact compatibilityA_row17
  · exact compatibilityA_row18
  · exact compatibilityA_row19
  · exact compatibilityA_row20
  · exact compatibilityA_row21
  · exact compatibilityA_row22
  · exact compatibilityA_row23
  · exact compatibilityA_row24
  · exact compatibilityA_row25
  · exact compatibilityA_row26
  · exact compatibilityA_row27
  · exact compatibilityA_row28
  · exact compatibilityA_row29
  · exact compatibilityA_row30
  · exact compatibilityA_row31
  · exact compatibilityA_row32
  · exact compatibilityA_row33
  · exact compatibilityA_row34
  · exact compatibilityA_row35
  · exact compatibilityA_row36
  · exact compatibilityA_row37
  · exact compatibilityA_row38
  · exact compatibilityA_row39
  · exact compatibilityA_row40
  · exact compatibilityA_row41
  · exact compatibilityA_row42
  · exact compatibilityA_row43
  · exact compatibilityA_row44
  · exact compatibilityA_row45
  · exact compatibilityA_row46
  · exact compatibilityA_row47
  · exact compatibilityA_row48
  · exact compatibilityA_row49
  · exact compatibilityA_row50
  · exact compatibilityA_row51
  · exact compatibilityA_row52
  · exact compatibilityA_row53
  · exact compatibilityA_row54
  · exact compatibilityA_row55
  · exact compatibilityA_row56
  · exact compatibilityA_row57
  · exact compatibilityA_row58

theorem compatibilityA_bound (i j : Nat) (hi : i < 59) (hj : j < 59) :
    idCompatible .hat i j = compatibleB (candidateAt .hat i) (candidateAt .hat j) := by
  exact compatibilityRow_sound .hat i (List.all_eq_true.mp compatibilityA_all i (List.mem_range.mpr hi)) j hj
end SpectreClusters.StageA
