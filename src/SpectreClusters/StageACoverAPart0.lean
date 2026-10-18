module

public import SpectreClusters.StageAWordModel

@[expose] public section

namespace SpectreClusters.StageA
open FiniteCoverWords

def suffixA0 : List (List Nat) := [[]]
set_option maxRecDepth 100000 in
theorem suffixA0_complete :
    enumerate (idCompatible .hat) ((choicesTable .hat).drop 19) = suffixA0 := by
  rfl
def suffixA1 : List (List Nat) := [[1],[12],[30],[56]]
set_option maxRecDepth 100000 in
theorem suffixA1_complete :
    enumerate (idCompatible .hat) ((choicesTable .hat).drop 18) = suffixA1 := by
  change extend (idCompatible .hat) [1,12,30,56]
    (enumerate (idCompatible .hat) ((choicesTable .hat).drop 19)) = suffixA1
  rw [suffixA0_complete]
  rfl
def suffixA2 : List (List Nat) := [[8,1],[14,1],[26,1],[40,1],[8,12],[14,12],[26,12],[40,12],[8,30],[14,30],[26,30],[40,30],[8,56],[14,56],[26,56],[40,56]]
set_option maxRecDepth 100000 in
theorem suffixA2_complete :
    enumerate (idCompatible .hat) ((choicesTable .hat).drop 17) = suffixA2 := by
  change extend (idCompatible .hat) [8,14,26,40]
    (enumerate (idCompatible .hat) ((choicesTable .hat).drop 18)) = suffixA2
  rw [suffixA1_complete]
  rfl
def suffixA3 : List (List Nat) := [[1,8,1],[1,14,1],[1,26,1],[1,40,1],[16,8,12],[16,14,12],[16,26,12],[16,40,12],[16,8,30],[16,14,30],[16,26,30],[16,40,30],[56,8,56],[56,14,56],[56,26,56],[56,40,56]]
set_option maxRecDepth 100000 in
theorem suffixA3_complete :
    enumerate (idCompatible .hat) ((choicesTable .hat).drop 16) = suffixA3 := by
  change extend (idCompatible .hat) [1,16,34,43,56]
    (enumerate (idCompatible .hat) ((choicesTable .hat).drop 17)) = suffixA3
  rw [suffixA2_complete]
  rfl
end SpectreClusters.StageA
