module

public import SpectreClusters.StageDRawProbeRowsT8HWordSplits
public import SpectreClusters.StageDRawProbeRowsT8HPart0
public import SpectreClusters.StageDRawProbeRowsT8HPart1
public import SpectreClusters.StageDRawProbeRowsT8HPart2
public import SpectreClusters.StageDRawProbeRowsT8HPart4
public import SpectreClusters.StageDRawProbeRowsT8HPart5
public import SpectreClusters.StageDRawProbeRowsT8HPart6
public import SpectreClusters.StageDRawProbeRowsT8HPart8
public import SpectreClusters.StageDRawProbeRowsT8HPart9
public import SpectreClusters.StageDRawProbeRowsT8HPart10
public import SpectreClusters.StageDRawProbeRowsT8HPart12
public import SpectreClusters.StageDRawProbeRowsT8HPart13
public import SpectreClusters.StageDRawProbeRowsT8HPart15
public import SpectreClusters.StageDRawProbeRowsT8HPart16
public import SpectreClusters.StageDRawProbeRowsT8HPart17
public import SpectreClusters.StageDRawProbeRowsT8HPart19
public import SpectreClusters.StageDRawProbeRowsT8HPart20
public import SpectreClusters.StageDRawProbeRowsT8HPart22
public import SpectreClusters.StageDRawProbeRowsT8HPart23
public import SpectreClusters.StageDRawProbeRowsT8HPart24
public import SpectreClusters.StageDRawProbeRowsT8HPart26
public import SpectreClusters.StageDRawProbeRowsT8HPart27
public import SpectreClusters.StageDRawProbeRowsT8HPart28
public import SpectreClusters.StageDRawProbeRowsT8HPart30
public import SpectreClusters.StageDRawProbeRowsT8HPart31
public import SpectreClusters.StageDRawProbeRowsT8HPart32
public import SpectreClusters.StageDRawProbeRowsT8HPart33
public import SpectreClusters.StageDRawProbeRowsT8HPart34
public import SpectreClusters.StageDRawProbeRowsT8HPart35
public import SpectreClusters.StageDRawProbeRowsT8HPart37
public import SpectreClusters.StageDRawProbeRowsT8HPart38
public import SpectreClusters.StageDRawProbeRowsT8HPart39
public import SpectreClusters.StageDRawProbeRowsT8HPart41
public import SpectreClusters.StageDRawProbeRowsT8HPart42
public import SpectreClusters.StageDRawProbeRowsT8HPart44
public import SpectreClusters.StageDRawProbeRowsT8HPart45
public import SpectreClusters.StageDRawProbeRowsT8HPart46
public import SpectreClusters.StageDRawProbeRowsT8HPart48
public import SpectreClusters.StageDRawProbeRowsT8HPart49
public import SpectreClusters.StageDRawProbeRowsT8HPart50
public import SpectreClusters.StageDRawProbeRowsT8HPart52
public import SpectreClusters.StageDRawProbeRowsT8HPart53
public import SpectreClusters.StageDRawProbeRowsT8HPart54
public import SpectreClusters.StageDRawProbeRowsT8HPart55
public import SpectreClusters.StageDRawProbeT8HStep15

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk0_words_binding :
    probeOutputT8H15Chunk0 = (probeRowWitnessesT8H0.map Prod.fst) ++ (probeRowWitnessesT8H1.map Prod.fst) ++ (probeRowWitnessesT8H2.map Prod.fst) ++ wordSplitT8H3Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk1_words_binding :
    probeOutputT8H15Chunk1 = wordSplitT8H3Right ++ (probeRowWitnessesT8H4.map Prod.fst) ++ (probeRowWitnessesT8H5.map Prod.fst) ++ (probeRowWitnessesT8H6.map Prod.fst) ++ wordSplitT8H7Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk2_words_binding :
    probeOutputT8H15Chunk2 = wordSplitT8H7Right ++ (probeRowWitnessesT8H8.map Prod.fst) ++ (probeRowWitnessesT8H9.map Prod.fst) ++ (probeRowWitnessesT8H10.map Prod.fst) ++ wordSplitT8H11Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk3_words_binding :
    probeOutputT8H15Chunk3 = wordSplitT8H11Right ++ (probeRowWitnessesT8H12.map Prod.fst) ++ (probeRowWitnessesT8H13.map Prod.fst) ++ wordSplitT8H14Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk4_words_binding :
    probeOutputT8H15Chunk4 = wordSplitT8H14Right ++ (probeRowWitnessesT8H15.map Prod.fst) ++ (probeRowWitnessesT8H16.map Prod.fst) ++ (probeRowWitnessesT8H17.map Prod.fst) ++ wordSplitT8H18Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk5_words_binding :
    probeOutputT8H15Chunk5 = wordSplitT8H18Right ++ (probeRowWitnessesT8H19.map Prod.fst) ++ (probeRowWitnessesT8H20.map Prod.fst) ++ wordSplitT8H21Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk6_words_binding :
    probeOutputT8H15Chunk6 = wordSplitT8H21Right ++ (probeRowWitnessesT8H22.map Prod.fst) ++ (probeRowWitnessesT8H23.map Prod.fst) ++ (probeRowWitnessesT8H24.map Prod.fst) ++ wordSplitT8H25Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk7_words_binding :
    probeOutputT8H15Chunk7 = wordSplitT8H25Right ++ (probeRowWitnessesT8H26.map Prod.fst) ++ (probeRowWitnessesT8H27.map Prod.fst) ++ (probeRowWitnessesT8H28.map Prod.fst) ++ wordSplitT8H29Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk8_words_binding :
    probeOutputT8H15Chunk8 = wordSplitT8H29Right ++ (probeRowWitnessesT8H30.map Prod.fst) ++ (probeRowWitnessesT8H31.map Prod.fst) ++ (probeRowWitnessesT8H32.map Prod.fst) := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk9_words_binding :
    probeOutputT8H15Chunk9 = (probeRowWitnessesT8H33.map Prod.fst) ++ (probeRowWitnessesT8H34.map Prod.fst) ++ (probeRowWitnessesT8H35.map Prod.fst) ++ wordSplitT8H36Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk10_words_binding :
    probeOutputT8H15Chunk10 = wordSplitT8H36Right ++ (probeRowWitnessesT8H37.map Prod.fst) ++ (probeRowWitnessesT8H38.map Prod.fst) ++ (probeRowWitnessesT8H39.map Prod.fst) ++ wordSplitT8H40Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk11_words_binding :
    probeOutputT8H15Chunk11 = wordSplitT8H40Right ++ (probeRowWitnessesT8H41.map Prod.fst) ++ (probeRowWitnessesT8H42.map Prod.fst) ++ wordSplitT8H43Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk12_words_binding :
    probeOutputT8H15Chunk12 = wordSplitT8H43Right ++ (probeRowWitnessesT8H44.map Prod.fst) ++ (probeRowWitnessesT8H45.map Prod.fst) ++ (probeRowWitnessesT8H46.map Prod.fst) ++ wordSplitT8H47Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk13_words_binding :
    probeOutputT8H15Chunk13 = wordSplitT8H47Right ++ (probeRowWitnessesT8H48.map Prod.fst) ++ (probeRowWitnessesT8H49.map Prod.fst) ++ (probeRowWitnessesT8H50.map Prod.fst) ++ wordSplitT8H51Left := by rfl
set_option maxRecDepth 100000 in
theorem probeOutputT8H15Chunk14_words_binding :
    probeOutputT8H15Chunk14 = wordSplitT8H51Right ++ (probeRowWitnessesT8H52.map Prod.fst) ++ (probeRowWitnessesT8H53.map Prod.fst) ++ (probeRowWitnessesT8H54.map Prod.fst) ++ (probeRowWitnessesT8H55.map Prod.fst) := by rfl
end SpectreClusters.StageD.Raw
