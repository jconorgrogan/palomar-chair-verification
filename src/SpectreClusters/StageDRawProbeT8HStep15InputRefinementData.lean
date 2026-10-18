module

public import SpectreClusters.StageDRawProbeT8HStep15Chunk0
public import SpectreClusters.StageDRawProbeT8HStep15Chunk1
public import SpectreClusters.StageDRawProbeT8HStep15Chunk2
public import SpectreClusters.StageDRawProbeT8HStep15Chunk3
public import SpectreClusters.StageDRawProbeT8HStep15Chunk4
public import SpectreClusters.StageDRawProbeT8HStep15Chunk5
public import SpectreClusters.StageDRawProbeT8HStep15Chunk6
public import SpectreClusters.StageDRawProbeT8HStep15Chunk7
public import SpectreClusters.StageDRawProbeT8HStep15Chunk8
public import SpectreClusters.StageDRawProbeT8HStep15Chunk9
public import SpectreClusters.StageDRawProbeT8HStep15Chunk10
public import SpectreClusters.StageDRawProbeT8HStep15Chunk11
public import SpectreClusters.StageDRawProbeT8HStep15Chunk12
public import SpectreClusters.StageDRawProbeT8HStep15Chunk13
public import SpectreClusters.StageDRawProbeT8HStep15Chunk14

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeT8H15InputPiece0 : List (List Nat) := probeInputT8H15Chunk0.take 88
def probeT8H15InputPiece1 : List (List Nat) := probeInputT8H15Chunk0.drop 88
def probeT8H15InputPiece2 : List (List Nat) := probeInputT8H15Chunk1.take 88
def probeT8H15InputPiece3 : List (List Nat) := probeInputT8H15Chunk1.drop 88
def probeT8H15InputPiece4 : List (List Nat) := probeInputT8H15Chunk2.take 56
def probeT8H15InputPiece5 : List (List Nat) := probeInputT8H15Chunk2.drop 56
def probeT8H15InputPiece6 : List (List Nat) := probeInputT8H15Chunk3.take 24
def probeT8H15InputPiece7 : List (List Nat) := probeInputT8H15Chunk3.drop 24
def probeT8H15InputPiece8 : List (List Nat) := probeInputT8H15Chunk4.take 24
def probeT8H15InputPiece9 : List (List Nat) := (probeInputT8H15Chunk4.drop 24).take 96
def probeT8H15InputPiece10 : List (List Nat) := probeInputT8H15Chunk4.drop 120
def probeT8H15InputPiece11 : List (List Nat) := probeInputT8H15Chunk5.take 120
def probeT8H15InputPiece12 : List (List Nat) := probeInputT8H15Chunk5.drop 120
def probeT8H15InputPiece13 : List (List Nat) := probeInputT8H15Chunk6.take 84
def probeT8H15InputPiece14 : List (List Nat) := probeInputT8H15Chunk6.drop 84
def probeT8H15InputPiece15 : List (List Nat) := probeInputT8H15Chunk7.take 64
def probeT8H15InputPiece16 : List (List Nat) := probeInputT8H15Chunk7.drop 64
def probeT8H15InputPiece17 : List (List Nat) := probeInputT8H15Chunk8.take 56
def probeT8H15InputPiece18 : List (List Nat) := probeInputT8H15Chunk8.drop 56
def probeT8H15InputPiece19 : List (List Nat) := probeInputT8H15Chunk9.take 14
def probeT8H15InputPiece20 : List (List Nat) := probeInputT8H15Chunk9.drop 14
def probeT8H15InputPiece21 : List (List Nat) := probeInputT8H15Chunk10.take 113
def probeT8H15InputPiece22 : List (List Nat) := probeInputT8H15Chunk10.drop 113
def probeT8H15InputPiece23 : List (List Nat) := probeInputT8H15Chunk11.take 96
def probeT8H15InputPiece24 : List (List Nat) := probeInputT8H15Chunk11.drop 96
def probeT8H15InputPiece25 : List (List Nat) := probeInputT8H15Chunk12.take 84
def probeT8H15InputPiece26 : List (List Nat) := probeInputT8H15Chunk12.drop 84
def probeT8H15InputPiece27 : List (List Nat) := probeInputT8H15Chunk13.take 62
def probeT8H15InputPiece28 : List (List Nat) := probeInputT8H15Chunk13.drop 62
def probeT8H15InputPiece29 : List (List Nat) := probeInputT8H15Chunk14.take 40
def probeT8H15InputPiece30 : List (List Nat) := probeInputT8H15Chunk14.drop 40
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk0_refinement :
    probeInputT8H15Chunk0 = probeT8H15InputPiece0 ++ probeT8H15InputPiece1 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk1_refinement :
    probeInputT8H15Chunk1 = probeT8H15InputPiece2 ++ probeT8H15InputPiece3 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk2_refinement :
    probeInputT8H15Chunk2 = probeT8H15InputPiece4 ++ probeT8H15InputPiece5 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk3_refinement :
    probeInputT8H15Chunk3 = probeT8H15InputPiece6 ++ probeT8H15InputPiece7 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk4_refinement :
    probeInputT8H15Chunk4 = probeT8H15InputPiece8 ++ probeT8H15InputPiece9 ++ probeT8H15InputPiece10 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk5_refinement :
    probeInputT8H15Chunk5 = probeT8H15InputPiece11 ++ probeT8H15InputPiece12 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk6_refinement :
    probeInputT8H15Chunk6 = probeT8H15InputPiece13 ++ probeT8H15InputPiece14 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk7_refinement :
    probeInputT8H15Chunk7 = probeT8H15InputPiece15 ++ probeT8H15InputPiece16 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk8_refinement :
    probeInputT8H15Chunk8 = probeT8H15InputPiece17 ++ probeT8H15InputPiece18 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk9_refinement :
    probeInputT8H15Chunk9 = probeT8H15InputPiece19 ++ probeT8H15InputPiece20 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk10_refinement :
    probeInputT8H15Chunk10 = probeT8H15InputPiece21 ++ probeT8H15InputPiece22 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk11_refinement :
    probeInputT8H15Chunk11 = probeT8H15InputPiece23 ++ probeT8H15InputPiece24 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk12_refinement :
    probeInputT8H15Chunk12 = probeT8H15InputPiece25 ++ probeT8H15InputPiece26 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk13_refinement :
    probeInputT8H15Chunk13 = probeT8H15InputPiece27 ++ probeT8H15InputPiece28 := by
  rfl
set_option maxRecDepth 100000 in
theorem probeInputT8H15Chunk14_refinement :
    probeInputT8H15Chunk14 = probeT8H15InputPiece29 ++ probeT8H15InputPiece30 := by
  rfl
end SpectreClusters.StageD.Raw
