module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H12 : List (List Nat × Nat) := [([187,187,187,187,107,191,191,191,191,48,48,118,155,118,118],547),([55,55,55,55,194,191,191,191,191,48,48,118,155,118,118],887),([144,144,144,144,194,191,191,191,191,48,48,118,155,118,118],1071),([187,187,187,187,194,191,191,191,191,48,48,118,155,118,118],1143),([55,55,55,55,239,191,191,191,191,48,48,118,155,118,118],1367),([144,144,144,144,239,191,191,191,191,48,48,118,155,118,118],1551),([187,187,187,187,239,191,191,191,191,48,48,118,155,118,118],1623),([55,55,55,55,107,236,236,236,236,48,48,118,155,118,118],292),([144,144,144,144,107,236,236,236,236,48,48,118,155,118,118],476),([187,187,187,187,107,236,236,236,236,48,48,118,155,118,118],548),([55,55,55,55,194,236,236,236,236,48,48,118,155,118,118],888),([144,144,144,144,194,236,236,236,236,48,48,118,155,118,118],1072),([187,187,187,187,194,236,236,236,236,48,48,118,155,118,118],1144),([55,55,55,55,239,236,236,236,236,48,48,118,155,118,118],1368),([144,144,144,144,239,236,236,236,236,48,48,118,155,118,118],1552),([187,187,187,187,239,236,236,236,236,48,48,118,155,118,118],1624),([55,55,55,55,85,85,37,37,37,116,116,118,155,118,118],104),([55,55,55,55,172,172,37,37,37,116,116,118,155,118,118],700),([55,55,55,55,40,104,104,104,104,116,116,118,155,118,118],10),([55,55,55,55,107,104,104,104,104,116,116,118,155,118,118],322),([55,55,55,55,194,104,104,104,104,116,116,118,155,118,118],918),([55,55,55,55,239,104,104,104,104,116,116,118,155,118,118],1398),([55,55,55,55,85,85,168,168,168,116,116,118,155,118,118],198),([55,55,55,55,172,172,168,168,168,116,116,118,155,118,118],794),([55,55,55,55,107,191,191,191,191,116,116,118,155,118,118],323),([55,55,55,55,194,191,191,191,191,116,116,118,155,118,118],919),([55,55,55,55,239,191,191,191,191,116,116,118,155,118,118],1399),([55,55,55,55,107,236,236,236,236,116,116,118,155,118,118],324),([55,55,55,55,194,236,236,236,236,116,116,118,155,118,118],920),([55,55,55,55,239,236,236,236,236,116,116,118,155,118,118],1400),([55,55,55,55,85,85,37,37,37,137,137,118,155,118,118],110),([144,144,144,144,85,85,37,37,37,137,137,118,155,118,118],144)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H12_part0 : ((probeRowWitnessesT8H12.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H12_part1 : ((probeRowWitnessesT8H12.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H12_part2 : ((probeRowWitnessesT8H12.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H12_part3 : ((probeRowWitnessesT8H12.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H12_checked : probeRowWitnessesT8H12.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H12.drop 0).take 8 ++ (probeRowWitnessesT8H12.drop 8).take 8 ++ (probeRowWitnessesT8H12.drop 16).take 8 ++ (probeRowWitnessesT8H12.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H12_part0,probeRowWitnessesT8H12_part1,probeRowWitnessesT8H12_part2,probeRowWitnessesT8H12_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
