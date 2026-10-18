module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H17 : List (List Nat × Nat) := [([123,123,28,123,239,104,104,104,104,28,28,118,244,118,118],1494),([256,256,28,256,239,104,104,104,104,28,28,118,244,118,118],1718),([123,123,28,123,85,85,168,168,168,28,28,118,244,118,118],220),([256,256,28,256,85,85,168,168,168,28,28,118,244,118,118],272),([123,123,28,123,172,172,168,168,168,28,28,118,244,118,118],816),([256,256,28,256,172,172,168,168,168,28,28,118,244,118,118],868),([123,123,28,123,107,191,191,191,191,28,28,118,244,118,118],419),([256,256,28,256,107,191,191,191,191,28,28,118,244,118,118],643),([123,123,28,123,194,191,191,191,191,28,28,118,244,118,118],1015),([256,256,28,256,194,191,191,191,191,28,28,118,244,118,118],1239),([123,123,28,123,239,191,191,191,191,28,28,118,244,118,118],1495),([256,256,28,256,239,191,191,191,191,28,28,118,244,118,118],1719),([123,123,28,123,107,236,236,236,236,28,28,118,244,118,118],420),([256,256,28,256,107,236,236,236,236,28,28,118,244,118,118],644),([123,123,28,123,194,236,236,236,236,28,28,118,244,118,118],1016),([256,256,28,256,194,236,236,236,236,28,28,118,244,118,118],1240),([123,123,28,123,239,236,236,236,236,28,28,118,244,118,118],1496),([256,256,28,256,239,236,236,236,236,28,28,118,244,118,118],1720),([55,55,55,55,85,85,37,37,37,48,48,118,244,118,118],98),([144,144,144,144,85,85,37,37,37,48,48,118,244,118,118],140),([187,187,187,187,85,85,37,37,37,48,48,118,244,118,118],158),([55,55,55,55,172,172,37,37,37,48,48,118,244,118,118],694),([144,144,144,144,172,172,37,37,37,48,48,118,244,118,118],736),([187,187,187,187,172,172,37,37,37,48,48,118,244,118,118],754),([100,100,100,217,217,217,37,37,37,48,48,118,244,118,118],1290),([232,232,232,217,217,217,37,37,37,48,48,118,244,118,118],1326),([55,55,55,55,40,104,104,104,104,48,48,118,244,118,118],4),([144,144,144,144,40,104,104,104,104,48,48,118,244,118,118],46),([187,187,187,187,40,104,104,104,104,48,48,118,244,118,118],64),([55,55,55,55,107,104,104,104,104,48,48,118,244,118,118],298),([144,144,144,144,107,104,104,104,104,48,48,118,244,118,118],482),([187,187,187,187,107,104,104,104,104,48,48,118,244,118,118],554)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H17_part0 : ((probeRowWitnessesT8H17.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H17_part1 : ((probeRowWitnessesT8H17.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H17_part2 : ((probeRowWitnessesT8H17.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H17_part3 : ((probeRowWitnessesT8H17.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H17_checked : probeRowWitnessesT8H17.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H17.drop 0).take 8 ++ (probeRowWitnessesT8H17.drop 8).take 8 ++ (probeRowWitnessesT8H17.drop 16).take 8 ++ (probeRowWitnessesT8H17.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H17_part0,probeRowWitnessesT8H17_part1,probeRowWitnessesT8H17_part2,probeRowWitnessesT8H17_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
