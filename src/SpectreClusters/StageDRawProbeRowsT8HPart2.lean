module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H2 : List (List Nat × Nat) := [([123,123,28,123,107,191,191,191,191,28,28,118,23,118,118],387),([256,256,28,256,107,191,191,191,191,28,28,118,23,118,118],611),([123,123,28,123,194,191,191,191,191,28,28,118,23,118,118],983),([256,256,28,256,194,191,191,191,191,28,28,118,23,118,118],1207),([123,123,28,123,239,191,191,191,191,28,28,118,23,118,118],1463),([256,256,28,256,239,191,191,191,191,28,28,118,23,118,118],1687),([123,123,28,123,107,236,236,236,236,28,28,118,23,118,118],388),([256,256,28,256,107,236,236,236,236,28,28,118,23,118,118],612),([123,123,28,123,194,236,236,236,236,28,28,118,23,118,118],984),([256,256,28,256,194,236,236,236,236,28,28,118,23,118,118],1208),([123,123,28,123,239,236,236,236,236,28,28,118,23,118,118],1464),([256,256,28,256,239,236,236,236,236,28,28,118,23,118,118],1688),([55,55,55,55,85,85,37,37,37,48,48,118,23,118,118],94),([144,144,144,144,85,85,37,37,37,48,48,118,23,118,118],136),([187,187,187,187,85,85,37,37,37,48,48,118,23,118,118],154),([55,55,55,55,172,172,37,37,37,48,48,118,23,118,118],690),([144,144,144,144,172,172,37,37,37,48,48,118,23,118,118],732),([187,187,187,187,172,172,37,37,37,48,48,118,23,118,118],750),([100,100,100,217,217,217,37,37,37,48,48,118,23,118,118],1286),([232,232,232,217,217,217,37,37,37,48,48,118,23,118,118],1322),([55,55,55,55,40,104,104,104,104,48,48,118,23,118,118],0),([144,144,144,144,40,104,104,104,104,48,48,118,23,118,118],42),([187,187,187,187,40,104,104,104,104,48,48,118,23,118,118],60),([55,55,55,55,107,104,104,104,104,48,48,118,23,118,118],282),([144,144,144,144,107,104,104,104,104,48,48,118,23,118,118],466),([187,187,187,187,107,104,104,104,104,48,48,118,23,118,118],538),([55,55,55,55,194,104,104,104,104,48,48,118,23,118,118],878),([144,144,144,144,194,104,104,104,104,48,48,118,23,118,118],1062),([187,187,187,187,194,104,104,104,104,48,48,118,23,118,118],1134),([55,55,55,55,239,104,104,104,104,48,48,118,23,118,118],1358),([144,144,144,144,239,104,104,104,104,48,48,118,23,118,118],1542),([187,187,187,187,239,104,104,104,104,48,48,118,23,118,118],1614)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H2_part0 : ((probeRowWitnessesT8H2.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H2_part1 : ((probeRowWitnessesT8H2.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H2_part2 : ((probeRowWitnessesT8H2.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H2_part3 : ((probeRowWitnessesT8H2.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H2_checked : probeRowWitnessesT8H2.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H2.drop 0).take 8 ++ (probeRowWitnessesT8H2.drop 8).take 8 ++ (probeRowWitnessesT8H2.drop 16).take 8 ++ (probeRowWitnessesT8H2.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H2_part0,probeRowWitnessesT8H2_part1,probeRowWitnessesT8H2_part2,probeRowWitnessesT8H2_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
