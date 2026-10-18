module

public import SpectreClusters.StageAWordModel

@[expose] public section

namespace SpectreClusters.StageA
open FiniteCoverWords

def suffixB0 : List (List Nat) := [[]]
set_option maxRecDepth 100000 in
theorem suffixB0_complete :
    enumerate (idCompatible .turtle) ((choicesTable .turtle).drop 21) = suffixB0 := by
  rfl
def suffixB1 : List (List Nat) := [[3],[29],[42],[62]]
set_option maxRecDepth 100000 in
theorem suffixB1_complete :
    enumerate (idCompatible .turtle) ((choicesTable .turtle).drop 20) = suffixB1 := by
  change extend (idCompatible .turtle) [3,29,42,62]
    (enumerate (idCompatible .turtle) ((choicesTable .turtle).drop 21)) = suffixB1
  rw [suffixB0_complete]
  rfl
def suffixB2 : List (List Nat) := [[11,3],[35,3],[41,3],[55,3],[11,29],[35,29],[41,29],[55,29],[11,42],[35,42],[41,42],[55,42],[11,62],[35,62],[41,62],[55,62]]
set_option maxRecDepth 100000 in
theorem suffixB2_complete :
    enumerate (idCompatible .turtle) ((choicesTable .turtle).drop 19) = suffixB2 := by
  change extend (idCompatible .turtle) [11,35,41,55]
    (enumerate (idCompatible .turtle) ((choicesTable .turtle).drop 20)) = suffixB2
  rw [suffixB1_complete]
  rfl
def suffixB3 : List (List Nat) := [[4,11,3],[9,11,3],[22,11,3],[32,11,3],[58,11,3],[4,35,3],[9,35,3],[22,35,3],[32,35,3],[58,35,3],[4,41,3],[9,41,3],[22,41,3],[32,41,3],[58,41,3],[4,55,3],[9,55,3],[22,55,3],[32,55,3],[58,55,3],[4,11,29],[9,11,29],[22,11,29],[32,11,29],[58,11,29],[4,35,29],[9,35,29],[22,35,29],[32,35,29],[58,35,29],[4,41,29],[9,41,29],[22,41,29],[32,41,29],[58,41,29],[4,55,29],[9,55,29],[22,55,29],[32,55,29],[58,55,29],[4,11,42],[9,11,42],[22,11,42],[32,11,42],[58,11,42],[4,35,42],[9,35,42],[22,35,42],[32,35,42],[58,35,42],[4,41,42],[9,41,42],[22,41,42],[32,41,42],[58,41,42],[4,55,42],[9,55,42],[22,55,42],[32,55,42],[58,55,42],[4,11,62],[9,11,62],[22,11,62],[32,11,62],[58,11,62],[4,35,62],[9,35,62],[22,35,62],[32,35,62],[58,35,62],[4,41,62],[9,41,62],[22,41,62],[32,41,62],[58,41,62],[4,55,62],[9,55,62],[22,55,62],[32,55,62],[58,55,62]]
set_option maxRecDepth 100000 in
theorem suffixB3_complete :
    enumerate (idCompatible .turtle) ((choicesTable .turtle).drop 18) = suffixB3 := by
  change extend (idCompatible .turtle) [4,9,22,32,58]
    (enumerate (idCompatible .turtle) ((choicesTable .turtle).drop 19)) = suffixB3
  rw [suffixB2_complete]
  rfl
end SpectreClusters.StageA
