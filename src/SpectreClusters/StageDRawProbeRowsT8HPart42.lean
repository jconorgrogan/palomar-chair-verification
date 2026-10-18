module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H42 : List (List Nat × Nat) := [([55,55,55,55,194,236,236,236,236,48,48,206,244,206,206],899),([144,144,144,144,194,236,236,236,236,48,48,206,244,206,206],1083),([187,187,187,187,194,236,236,236,236,48,48,206,244,206,206],1155),([55,55,55,55,239,236,236,236,236,48,48,206,244,206,206],1379),([144,144,144,144,239,236,236,236,236,48,48,206,244,206,206],1563),([187,187,187,187,239,236,236,236,236,48,48,206,244,206,206],1635),([55,55,55,55,85,85,37,37,37,116,116,206,244,206,206],107),([55,55,55,55,172,172,37,37,37,116,116,206,244,206,206],703),([55,55,55,55,40,104,104,104,104,116,116,206,244,206,206],13),([55,55,55,55,107,104,104,104,104,116,116,206,244,206,206],333),([55,55,55,55,194,104,104,104,104,116,116,206,244,206,206],929),([55,55,55,55,239,104,104,104,104,116,116,206,244,206,206],1409),([55,55,55,55,85,85,168,168,168,116,116,206,244,206,206],201),([55,55,55,55,172,172,168,168,168,116,116,206,244,206,206],797),([55,55,55,55,107,191,191,191,191,116,116,206,244,206,206],334),([55,55,55,55,194,191,191,191,191,116,116,206,244,206,206],930),([55,55,55,55,239,191,191,191,191,116,116,206,244,206,206],1410),([55,55,55,55,107,236,236,236,236,116,116,206,244,206,206],335),([55,55,55,55,194,236,236,236,236,116,116,206,244,206,206],931),([55,55,55,55,239,236,236,236,236,116,116,206,244,206,206],1411),([55,55,55,55,85,85,37,37,37,137,137,206,244,206,206],113),([144,144,144,144,85,85,37,37,37,137,137,206,244,206,206],147),([187,187,187,187,85,85,37,37,37,137,137,206,244,206,206],165),([55,55,55,55,172,172,37,37,37,137,137,206,244,206,206],709),([144,144,144,144,172,172,37,37,37,137,137,206,244,206,206],743),([187,187,187,187,172,172,37,37,37,137,137,206,244,206,206],761),([100,100,100,217,217,217,37,37,37,137,137,206,244,206,206],1297),([232,232,232,217,217,217,37,37,37,137,137,206,244,206,206],1333),([55,55,55,55,40,104,104,104,104,137,137,206,244,206,206],19),([144,144,144,144,40,104,104,104,104,137,137,206,244,206,206],53),([187,187,187,187,40,104,104,104,104,137,137,206,244,206,206],71),([55,55,55,55,107,104,104,104,104,137,137,206,244,206,206],357)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H42_part0 : ((probeRowWitnessesT8H42.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H42_part1 : ((probeRowWitnessesT8H42.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H42_part2 : ((probeRowWitnessesT8H42.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H42_part3 : ((probeRowWitnessesT8H42.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H42_checked : probeRowWitnessesT8H42.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H42.drop 0).take 8 ++ (probeRowWitnessesT8H42.drop 8).take 8 ++ (probeRowWitnessesT8H42.drop 16).take 8 ++ (probeRowWitnessesT8H42.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H42_part0,probeRowWitnessesT8H42_part1,probeRowWitnessesT8H42_part2,probeRowWitnessesT8H42_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
