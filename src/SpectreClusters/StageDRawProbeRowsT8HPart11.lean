module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H11 : List (List Nat × Nat) := [([123,123,28,123,239,236,236,236,236,28,28,118,155,118,118],1484),([256,256,28,256,239,236,236,236,236,28,28,118,155,118,118],1708),([55,55,55,55,85,85,37,37,37,48,48,118,155,118,118],96),([144,144,144,144,85,85,37,37,37,48,48,118,155,118,118],138),([187,187,187,187,85,85,37,37,37,48,48,118,155,118,118],156),([55,55,55,55,172,172,37,37,37,48,48,118,155,118,118],692),([144,144,144,144,172,172,37,37,37,48,48,118,155,118,118],734),([187,187,187,187,172,172,37,37,37,48,48,118,155,118,118],752),([100,100,100,217,217,217,37,37,37,48,48,118,155,118,118],1288),([232,232,232,217,217,217,37,37,37,48,48,118,155,118,118],1324),([55,55,55,55,40,104,104,104,104,48,48,118,155,118,118],2),([144,144,144,144,40,104,104,104,104,48,48,118,155,118,118],44),([187,187,187,187,40,104,104,104,104,48,48,118,155,118,118],62),([55,55,55,55,107,104,104,104,104,48,48,118,155,118,118],290),([144,144,144,144,107,104,104,104,104,48,48,118,155,118,118],474),([187,187,187,187,107,104,104,104,104,48,48,118,155,118,118],546),([55,55,55,55,194,104,104,104,104,48,48,118,155,118,118],886),([144,144,144,144,194,104,104,104,104,48,48,118,155,118,118],1070),([187,187,187,187,194,104,104,104,104,48,48,118,155,118,118],1142),([55,55,55,55,239,104,104,104,104,48,48,118,155,118,118],1366),([144,144,144,144,239,104,104,104,104,48,48,118,155,118,118],1550),([187,187,187,187,239,104,104,104,104,48,48,118,155,118,118],1622),([55,55,55,55,85,85,168,168,168,48,48,118,155,118,118],190),([144,144,144,144,85,85,168,168,168,48,48,118,155,118,118],232),([187,187,187,187,85,85,168,168,168,48,48,118,155,118,118],250),([55,55,55,55,172,172,168,168,168,48,48,118,155,118,118],786),([144,144,144,144,172,172,168,168,168,48,48,118,155,118,118],828),([187,187,187,187,172,172,168,168,168,48,48,118,155,118,118],846),([100,100,100,217,217,217,168,168,168,48,48,118,155,118,118],1306),([232,232,232,217,217,217,168,168,168,48,48,118,155,118,118],1342),([55,55,55,55,107,191,191,191,191,48,48,118,155,118,118],291),([144,144,144,144,107,191,191,191,191,48,48,118,155,118,118],475)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H11_part0 : ((probeRowWitnessesT8H11.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H11_part1 : ((probeRowWitnessesT8H11.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H11_part2 : ((probeRowWitnessesT8H11.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H11_part3 : ((probeRowWitnessesT8H11.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H11_checked : probeRowWitnessesT8H11.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H11.drop 0).take 8 ++ (probeRowWitnessesT8H11.drop 8).take 8 ++ (probeRowWitnessesT8H11.drop 16).take 8 ++ (probeRowWitnessesT8H11.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H11_part0,probeRowWitnessesT8H11_part1,probeRowWitnessesT8H11_part2,probeRowWitnessesT8H11_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
