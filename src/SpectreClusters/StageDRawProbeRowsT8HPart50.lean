module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H50 : List (List Nat × Nat) := [([123,123,28,123,194,16,16,16,251,28,28,251,155,251,251],1008),([256,256,28,256,194,16,16,16,251,28,28,251,155,251,251],1232),([123,123,28,123,239,16,16,16,251,28,28,251,155,251,251],1488),([256,256,28,256,239,16,16,16,251,28,28,251,155,251,251],1712),([123,123,28,123,107,148,148,148,251,28,28,251,155,251,251],413),([256,256,28,256,107,148,148,148,251,28,28,251,155,251,251],637),([123,123,28,123,194,148,148,148,251,28,28,251,155,251,251],1009),([256,256,28,256,194,148,148,148,251,28,28,251,155,251,251],1233),([123,123,28,123,239,148,148,148,251,28,28,251,155,251,251],1489),([256,256,28,256,239,148,148,148,251,28,28,251,155,251,251],1713),([55,55,55,55,107,16,16,16,251,48,48,251,155,251,251],296),([144,144,144,144,107,16,16,16,251,48,48,251,155,251,251],480),([187,187,187,187,107,16,16,16,251,48,48,251,155,251,251],552),([55,55,55,55,194,16,16,16,251,48,48,251,155,251,251],892),([144,144,144,144,194,16,16,16,251,48,48,251,155,251,251],1076),([187,187,187,187,194,16,16,16,251,48,48,251,155,251,251],1148),([55,55,55,55,239,16,16,16,251,48,48,251,155,251,251],1372),([144,144,144,144,239,16,16,16,251,48,48,251,155,251,251],1556),([187,187,187,187,239,16,16,16,251,48,48,251,155,251,251],1628),([55,55,55,55,107,148,148,148,251,48,48,251,155,251,251],297),([144,144,144,144,107,148,148,148,251,48,48,251,155,251,251],481),([187,187,187,187,107,148,148,148,251,48,48,251,155,251,251],553),([55,55,55,55,194,148,148,148,251,48,48,251,155,251,251],893),([144,144,144,144,194,148,148,148,251,48,48,251,155,251,251],1077),([187,187,187,187,194,148,148,148,251,48,48,251,155,251,251],1149),([55,55,55,55,239,148,148,148,251,48,48,251,155,251,251],1373),([144,144,144,144,239,148,148,148,251,48,48,251,155,251,251],1557),([187,187,187,187,239,148,148,148,251,48,48,251,155,251,251],1629),([55,55,55,55,107,16,16,16,251,116,116,251,155,251,251],328),([55,55,55,55,194,16,16,16,251,116,116,251,155,251,251],924),([55,55,55,55,239,16,16,16,251,116,116,251,155,251,251],1404),([55,55,55,55,107,148,148,148,251,116,116,251,155,251,251],329)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H50_part0 : ((probeRowWitnessesT8H50.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H50_part1 : ((probeRowWitnessesT8H50.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H50_part2 : ((probeRowWitnessesT8H50.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H50_part3 : ((probeRowWitnessesT8H50.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H50_checked : probeRowWitnessesT8H50.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H50.drop 0).take 8 ++ (probeRowWitnessesT8H50.drop 8).take 8 ++ (probeRowWitnessesT8H50.drop 16).take 8 ++ (probeRowWitnessesT8H50.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H50_part0,probeRowWitnessesT8H50_part1,probeRowWitnessesT8H50_part2,probeRowWitnessesT8H50_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
