module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H19 : List (List Nat × Nat) := [([55,55,55,55,85,85,37,37,37,116,116,118,244,118,118],106),([55,55,55,55,172,172,37,37,37,116,116,118,244,118,118],702),([55,55,55,55,40,104,104,104,104,116,116,118,244,118,118],12),([55,55,55,55,107,104,104,104,104,116,116,118,244,118,118],330),([55,55,55,55,194,104,104,104,104,116,116,118,244,118,118],926),([55,55,55,55,239,104,104,104,104,116,116,118,244,118,118],1406),([55,55,55,55,85,85,168,168,168,116,116,118,244,118,118],200),([55,55,55,55,172,172,168,168,168,116,116,118,244,118,118],796),([55,55,55,55,107,191,191,191,191,116,116,118,244,118,118],331),([55,55,55,55,194,191,191,191,191,116,116,118,244,118,118],927),([55,55,55,55,239,191,191,191,191,116,116,118,244,118,118],1407),([55,55,55,55,107,236,236,236,236,116,116,118,244,118,118],332),([55,55,55,55,194,236,236,236,236,116,116,118,244,118,118],928),([55,55,55,55,239,236,236,236,236,116,116,118,244,118,118],1408),([55,55,55,55,85,85,37,37,37,137,137,118,244,118,118],112),([144,144,144,144,85,85,37,37,37,137,137,118,244,118,118],146),([187,187,187,187,85,85,37,37,37,137,137,118,244,118,118],164),([55,55,55,55,172,172,37,37,37,137,137,118,244,118,118],708),([144,144,144,144,172,172,37,37,37,137,137,118,244,118,118],742),([187,187,187,187,172,172,37,37,37,137,137,118,244,118,118],760),([100,100,100,217,217,217,37,37,37,137,137,118,244,118,118],1296),([232,232,232,217,217,217,37,37,37,137,137,118,244,118,118],1332),([55,55,55,55,40,104,104,104,104,137,137,118,244,118,118],18),([144,144,144,144,40,104,104,104,104,137,137,118,244,118,118],52),([187,187,187,187,40,104,104,104,104,137,137,118,244,118,118],70),([55,55,55,55,107,104,104,104,104,137,137,118,244,118,118],354),([144,144,144,144,107,104,104,104,104,137,137,118,244,118,118],506),([187,187,187,187,107,104,104,104,104,137,137,118,244,118,118],578),([55,55,55,55,194,104,104,104,104,137,137,118,244,118,118],950),([144,144,144,144,194,104,104,104,104,137,137,118,244,118,118],1102),([187,187,187,187,194,104,104,104,104,137,137,118,244,118,118],1174),([55,55,55,55,239,104,104,104,104,137,137,118,244,118,118],1430)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H19_part0 : ((probeRowWitnessesT8H19.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H19_part1 : ((probeRowWitnessesT8H19.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H19_part2 : ((probeRowWitnessesT8H19.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H19_part3 : ((probeRowWitnessesT8H19.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H19_checked : probeRowWitnessesT8H19.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H19.drop 0).take 8 ++ (probeRowWitnessesT8H19.drop 8).take 8 ++ (probeRowWitnessesT8H19.drop 16).take 8 ++ (probeRowWitnessesT8H19.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H19_part0,probeRowWitnessesT8H19_part1,probeRowWitnessesT8H19_part2,probeRowWitnessesT8H19_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
