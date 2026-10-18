module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H0 : List (List Nat × Nat) := [([123,123,28,123,107,16,16,16,30,28,28,45,45,30,30],394),([256,256,28,256,107,16,16,16,30,28,28,45,45,30,30],618),([123,123,28,123,194,16,16,16,30,28,28,45,45,30,30],990),([256,256,28,256,194,16,16,16,30,28,28,45,45,30,30],1214),([123,123,28,123,239,16,16,16,30,28,28,45,45,30,30],1470),([256,256,28,256,239,16,16,16,30,28,28,45,45,30,30],1694),([123,123,28,123,107,148,148,148,30,28,28,45,45,30,30],395),([256,256,28,256,107,148,148,148,30,28,28,45,45,30,30],619),([123,123,28,123,194,148,148,148,30,28,28,45,45,30,30],991),([256,256,28,256,194,148,148,148,30,28,28,45,45,30,30],1215),([123,123,28,123,239,148,148,148,30,28,28,45,45,30,30],1471),([256,256,28,256,239,148,148,148,30,28,28,45,45,30,30],1695),([123,123,95,123,107,16,16,16,30,95,114,114,114,30,30],426),([256,256,95,256,107,16,16,16,30,95,114,114,114,30,30],650),([123,123,95,123,194,16,16,16,30,95,114,114,114,30,30],1022),([256,256,95,256,194,16,16,16,30,95,114,114,114,30,30],1246),([123,123,95,123,239,16,16,16,30,95,114,114,114,30,30],1502),([256,256,95,256,239,16,16,16,30,95,114,114,114,30,30],1726),([123,123,95,123,107,148,148,148,30,95,114,114,114,30,30],427),([256,256,95,256,107,148,148,148,30,95,114,114,114,30,30],651),([123,123,95,123,194,148,148,148,30,95,114,114,114,30,30],1023),([256,256,95,256,194,148,148,148,30,95,114,114,114,30,30],1247),([123,123,95,123,239,148,148,148,30,95,114,114,114,30,30],1503),([256,256,95,256,239,148,148,148,30,95,114,114,114,30,30],1727),([123,123,228,123,107,16,16,16,30,228,114,114,114,30,30],430),([256,256,228,256,107,16,16,16,30,228,114,114,114,30,30],654),([123,123,228,123,194,16,16,16,30,228,114,114,114,30,30],1026),([256,256,228,256,194,16,16,16,30,228,114,114,114,30,30],1250),([123,123,228,123,239,16,16,16,30,228,114,114,114,30,30],1506),([256,256,228,256,239,16,16,16,30,228,114,114,114,30,30],1730),([123,123,228,123,107,148,148,148,30,228,114,114,114,30,30],431),([256,256,228,256,107,148,148,148,30,228,114,114,114,30,30],655)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H0_part0 : ((probeRowWitnessesT8H0.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H0_part1 : ((probeRowWitnessesT8H0.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H0_part2 : ((probeRowWitnessesT8H0.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H0_part3 : ((probeRowWitnessesT8H0.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H0_checked : probeRowWitnessesT8H0.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H0.drop 0).take 8 ++ (probeRowWitnessesT8H0.drop 8).take 8 ++ (probeRowWitnessesT8H0.drop 16).take 8 ++ (probeRowWitnessesT8H0.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H0_part0,probeRowWitnessesT8H0_part1,probeRowWitnessesT8H0_part2,probeRowWitnessesT8H0_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
