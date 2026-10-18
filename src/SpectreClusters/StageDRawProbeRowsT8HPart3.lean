module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H3 : List (List Nat × Nat) := [([55,55,55,55,85,85,168,168,168,48,48,118,23,118,118],188),([144,144,144,144,85,85,168,168,168,48,48,118,23,118,118],230),([187,187,187,187,85,85,168,168,168,48,48,118,23,118,118],248),([55,55,55,55,172,172,168,168,168,48,48,118,23,118,118],784),([144,144,144,144,172,172,168,168,168,48,48,118,23,118,118],826),([187,187,187,187,172,172,168,168,168,48,48,118,23,118,118],844),([100,100,100,217,217,217,168,168,168,48,48,118,23,118,118],1304),([232,232,232,217,217,217,168,168,168,48,48,118,23,118,118],1340),([55,55,55,55,107,191,191,191,191,48,48,118,23,118,118],283),([144,144,144,144,107,191,191,191,191,48,48,118,23,118,118],467),([187,187,187,187,107,191,191,191,191,48,48,118,23,118,118],539),([55,55,55,55,194,191,191,191,191,48,48,118,23,118,118],879),([144,144,144,144,194,191,191,191,191,48,48,118,23,118,118],1063),([187,187,187,187,194,191,191,191,191,48,48,118,23,118,118],1135),([55,55,55,55,239,191,191,191,191,48,48,118,23,118,118],1359),([144,144,144,144,239,191,191,191,191,48,48,118,23,118,118],1543),([187,187,187,187,239,191,191,191,191,48,48,118,23,118,118],1615),([55,55,55,55,107,236,236,236,236,48,48,118,23,118,118],284),([144,144,144,144,107,236,236,236,236,48,48,118,23,118,118],468),([187,187,187,187,107,236,236,236,236,48,48,118,23,118,118],540),([55,55,55,55,194,236,236,236,236,48,48,118,23,118,118],880),([144,144,144,144,194,236,236,236,236,48,48,118,23,118,118],1064),([187,187,187,187,194,236,236,236,236,48,48,118,23,118,118],1136),([55,55,55,55,239,236,236,236,236,48,48,118,23,118,118],1360),([144,144,144,144,239,236,236,236,236,48,48,118,23,118,118],1544),([187,187,187,187,239,236,236,236,236,48,48,118,23,118,118],1616),([55,55,55,55,85,85,37,37,37,116,116,118,23,118,118],100),([55,55,55,55,172,172,37,37,37,116,116,118,23,118,118],696),([55,55,55,55,40,104,104,104,104,116,116,118,23,118,118],6),([55,55,55,55,107,104,104,104,104,116,116,118,23,118,118],306),([55,55,55,55,194,104,104,104,104,116,116,118,23,118,118],902),([55,55,55,55,239,104,104,104,104,116,116,118,23,118,118],1382)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H3_part0 : ((probeRowWitnessesT8H3.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H3_part1 : ((probeRowWitnessesT8H3.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H3_part2 : ((probeRowWitnessesT8H3.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H3_part3 : ((probeRowWitnessesT8H3.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H3_checked : probeRowWitnessesT8H3.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H3.drop 0).take 8 ++ (probeRowWitnessesT8H3.drop 8).take 8 ++ (probeRowWitnessesT8H3.drop 16).take 8 ++ (probeRowWitnessesT8H3.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H3_part0,probeRowWitnessesT8H3_part1,probeRowWitnessesT8H3_part2,probeRowWitnessesT8H3_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
