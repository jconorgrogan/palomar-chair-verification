module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H26 : List (List Nat × Nat) := [([55,55,55,55,194,104,104,104,104,48,48,206,23,206,206],881),([144,144,144,144,194,104,104,104,104,48,48,206,23,206,206],1065),([187,187,187,187,194,104,104,104,104,48,48,206,23,206,206],1137),([55,55,55,55,239,104,104,104,104,48,48,206,23,206,206],1361),([144,144,144,144,239,104,104,104,104,48,48,206,23,206,206],1545),([187,187,187,187,239,104,104,104,104,48,48,206,23,206,206],1617),([55,55,55,55,85,85,168,168,168,48,48,206,23,206,206],189),([144,144,144,144,85,85,168,168,168,48,48,206,23,206,206],231),([187,187,187,187,85,85,168,168,168,48,48,206,23,206,206],249),([55,55,55,55,172,172,168,168,168,48,48,206,23,206,206],785),([144,144,144,144,172,172,168,168,168,48,48,206,23,206,206],827),([187,187,187,187,172,172,168,168,168,48,48,206,23,206,206],845),([100,100,100,217,217,217,168,168,168,48,48,206,23,206,206],1305),([232,232,232,217,217,217,168,168,168,48,48,206,23,206,206],1341),([55,55,55,55,107,191,191,191,191,48,48,206,23,206,206],286),([144,144,144,144,107,191,191,191,191,48,48,206,23,206,206],470),([187,187,187,187,107,191,191,191,191,48,48,206,23,206,206],542),([55,55,55,55,194,191,191,191,191,48,48,206,23,206,206],882),([144,144,144,144,194,191,191,191,191,48,48,206,23,206,206],1066),([187,187,187,187,194,191,191,191,191,48,48,206,23,206,206],1138),([55,55,55,55,239,191,191,191,191,48,48,206,23,206,206],1362),([144,144,144,144,239,191,191,191,191,48,48,206,23,206,206],1546),([187,187,187,187,239,191,191,191,191,48,48,206,23,206,206],1618),([55,55,55,55,107,236,236,236,236,48,48,206,23,206,206],287),([144,144,144,144,107,236,236,236,236,48,48,206,23,206,206],471),([187,187,187,187,107,236,236,236,236,48,48,206,23,206,206],543),([55,55,55,55,194,236,236,236,236,48,48,206,23,206,206],883),([144,144,144,144,194,236,236,236,236,48,48,206,23,206,206],1067),([187,187,187,187,194,236,236,236,236,48,48,206,23,206,206],1139),([55,55,55,55,239,236,236,236,236,48,48,206,23,206,206],1363),([144,144,144,144,239,236,236,236,236,48,48,206,23,206,206],1547),([187,187,187,187,239,236,236,236,236,48,48,206,23,206,206],1619)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H26_part0 : ((probeRowWitnessesT8H26.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H26_part1 : ((probeRowWitnessesT8H26.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H26_part2 : ((probeRowWitnessesT8H26.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H26_part3 : ((probeRowWitnessesT8H26.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H26_checked : probeRowWitnessesT8H26.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H26.drop 0).take 8 ++ (probeRowWitnessesT8H26.drop 8).take 8 ++ (probeRowWitnessesT8H26.drop 16).take 8 ++ (probeRowWitnessesT8H26.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H26_part0,probeRowWitnessesT8H26_part1,probeRowWitnessesT8H26_part2,probeRowWitnessesT8H26_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
