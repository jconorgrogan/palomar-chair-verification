module

public import SpectreClusters.StageDRawProbeRowsT8HPart3
public import SpectreClusters.StageDRawProbeRowsT8HPart7
public import SpectreClusters.StageDRawProbeRowsT8HPart11
public import SpectreClusters.StageDRawProbeRowsT8HPart14
public import SpectreClusters.StageDRawProbeRowsT8HPart18
public import SpectreClusters.StageDRawProbeRowsT8HPart21
public import SpectreClusters.StageDRawProbeRowsT8HPart25
public import SpectreClusters.StageDRawProbeRowsT8HPart29
public import SpectreClusters.StageDRawProbeRowsT8HPart36
public import SpectreClusters.StageDRawProbeRowsT8HPart40
public import SpectreClusters.StageDRawProbeRowsT8HPart43
public import SpectreClusters.StageDRawProbeRowsT8HPart47
public import SpectreClusters.StageDRawProbeRowsT8HPart51

@[expose] public section

namespace SpectreClusters.StageD.Raw
def wordSplitT8H3Left : List (List Nat) := (probeRowWitnessesT8H3.map Prod.fst).take 24
def wordSplitT8H3Right : List (List Nat) := (probeRowWitnessesT8H3.map Prod.fst).drop 24
def wordSplitT8H7Left : List (List Nat) := (probeRowWitnessesT8H7.map Prod.fst).take 8
def wordSplitT8H7Right : List (List Nat) := (probeRowWitnessesT8H7.map Prod.fst).drop 8
def wordSplitT8H11Left : List (List Nat) := (probeRowWitnessesT8H11.map Prod.fst).take 8
def wordSplitT8H11Right : List (List Nat) := (probeRowWitnessesT8H11.map Prod.fst).drop 8
def wordSplitT8H14Left : List (List Nat) := (probeRowWitnessesT8H14.map Prod.fst).take 20
def wordSplitT8H14Right : List (List Nat) := (probeRowWitnessesT8H14.map Prod.fst).drop 20
def wordSplitT8H18Left : List (List Nat) := (probeRowWitnessesT8H18.map Prod.fst).take 12
def wordSplitT8H18Right : List (List Nat) := (probeRowWitnessesT8H18.map Prod.fst).drop 12
def wordSplitT8H21Left : List (List Nat) := (probeRowWitnessesT8H21.map Prod.fst).take 24
def wordSplitT8H21Right : List (List Nat) := (probeRowWitnessesT8H21.map Prod.fst).drop 24
def wordSplitT8H25Left : List (List Nat) := (probeRowWitnessesT8H25.map Prod.fst).take 24
def wordSplitT8H25Right : List (List Nat) := (probeRowWitnessesT8H25.map Prod.fst).drop 24
def wordSplitT8H29Left : List (List Nat) := (probeRowWitnessesT8H29.map Prod.fst).take 4
def wordSplitT8H29Right : List (List Nat) := (probeRowWitnessesT8H29.map Prod.fst).drop 4
def wordSplitT8H36Left : List (List Nat) := (probeRowWitnessesT8H36.map Prod.fst).take 20
def wordSplitT8H36Right : List (List Nat) := (probeRowWitnessesT8H36.map Prod.fst).drop 20
def wordSplitT8H40Left : List (List Nat) := (probeRowWitnessesT8H40.map Prod.fst).take 8
def wordSplitT8H40Right : List (List Nat) := (probeRowWitnessesT8H40.map Prod.fst).drop 8
def wordSplitT8H43Left : List (List Nat) := (probeRowWitnessesT8H43.map Prod.fst).take 24
def wordSplitT8H43Right : List (List Nat) := (probeRowWitnessesT8H43.map Prod.fst).drop 24
def wordSplitT8H47Left : List (List Nat) := (probeRowWitnessesT8H47.map Prod.fst).take 16
def wordSplitT8H47Right : List (List Nat) := (probeRowWitnessesT8H47.map Prod.fst).drop 16
def wordSplitT8H51Left : List (List Nat) := (probeRowWitnessesT8H51.map Prod.fst).take 16
def wordSplitT8H51Right : List (List Nat) := (probeRowWitnessesT8H51.map Prod.fst).drop 16
theorem probeRowWitnessesT8H3_words_split :
    probeRowWitnessesT8H3.map Prod.fst = wordSplitT8H3Left ++ wordSplitT8H3Right := by
  exact (List.take_append_drop 24 (probeRowWitnessesT8H3.map Prod.fst)).symm
theorem probeRowWitnessesT8H7_words_split :
    probeRowWitnessesT8H7.map Prod.fst = wordSplitT8H7Left ++ wordSplitT8H7Right := by
  exact (List.take_append_drop 8 (probeRowWitnessesT8H7.map Prod.fst)).symm
theorem probeRowWitnessesT8H11_words_split :
    probeRowWitnessesT8H11.map Prod.fst = wordSplitT8H11Left ++ wordSplitT8H11Right := by
  exact (List.take_append_drop 8 (probeRowWitnessesT8H11.map Prod.fst)).symm
theorem probeRowWitnessesT8H14_words_split :
    probeRowWitnessesT8H14.map Prod.fst = wordSplitT8H14Left ++ wordSplitT8H14Right := by
  exact (List.take_append_drop 20 (probeRowWitnessesT8H14.map Prod.fst)).symm
theorem probeRowWitnessesT8H18_words_split :
    probeRowWitnessesT8H18.map Prod.fst = wordSplitT8H18Left ++ wordSplitT8H18Right := by
  exact (List.take_append_drop 12 (probeRowWitnessesT8H18.map Prod.fst)).symm
theorem probeRowWitnessesT8H21_words_split :
    probeRowWitnessesT8H21.map Prod.fst = wordSplitT8H21Left ++ wordSplitT8H21Right := by
  exact (List.take_append_drop 24 (probeRowWitnessesT8H21.map Prod.fst)).symm
theorem probeRowWitnessesT8H25_words_split :
    probeRowWitnessesT8H25.map Prod.fst = wordSplitT8H25Left ++ wordSplitT8H25Right := by
  exact (List.take_append_drop 24 (probeRowWitnessesT8H25.map Prod.fst)).symm
theorem probeRowWitnessesT8H29_words_split :
    probeRowWitnessesT8H29.map Prod.fst = wordSplitT8H29Left ++ wordSplitT8H29Right := by
  exact (List.take_append_drop 4 (probeRowWitnessesT8H29.map Prod.fst)).symm
theorem probeRowWitnessesT8H36_words_split :
    probeRowWitnessesT8H36.map Prod.fst = wordSplitT8H36Left ++ wordSplitT8H36Right := by
  exact (List.take_append_drop 20 (probeRowWitnessesT8H36.map Prod.fst)).symm
theorem probeRowWitnessesT8H40_words_split :
    probeRowWitnessesT8H40.map Prod.fst = wordSplitT8H40Left ++ wordSplitT8H40Right := by
  exact (List.take_append_drop 8 (probeRowWitnessesT8H40.map Prod.fst)).symm
theorem probeRowWitnessesT8H43_words_split :
    probeRowWitnessesT8H43.map Prod.fst = wordSplitT8H43Left ++ wordSplitT8H43Right := by
  exact (List.take_append_drop 24 (probeRowWitnessesT8H43.map Prod.fst)).symm
theorem probeRowWitnessesT8H47_words_split :
    probeRowWitnessesT8H47.map Prod.fst = wordSplitT8H47Left ++ wordSplitT8H47Right := by
  exact (List.take_append_drop 16 (probeRowWitnessesT8H47.map Prod.fst)).symm
theorem probeRowWitnessesT8H51_words_split :
    probeRowWitnessesT8H51.map Prod.fst = wordSplitT8H51Left ++ wordSplitT8H51Right := by
  exact (List.take_append_drop 16 (probeRowWitnessesT8H51.map Prod.fst)).symm
end SpectreClusters.StageD.Raw
