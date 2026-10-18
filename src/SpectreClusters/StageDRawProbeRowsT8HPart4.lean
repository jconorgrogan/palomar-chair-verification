module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H4 : List (List Nat × Nat) := [([55,55,55,55,85,85,168,168,168,116,116,118,23,118,118],194),([55,55,55,55,172,172,168,168,168,116,116,118,23,118,118],790),([55,55,55,55,107,191,191,191,191,116,116,118,23,118,118],307),([55,55,55,55,194,191,191,191,191,116,116,118,23,118,118],903),([55,55,55,55,239,191,191,191,191,116,116,118,23,118,118],1383),([55,55,55,55,107,236,236,236,236,116,116,118,23,118,118],308),([55,55,55,55,194,236,236,236,236,116,116,118,23,118,118],904),([55,55,55,55,239,236,236,236,236,116,116,118,23,118,118],1384),([55,55,55,55,85,85,37,37,37,137,137,118,23,118,118],108),([144,144,144,144,85,85,37,37,37,137,137,118,23,118,118],142),([187,187,187,187,85,85,37,37,37,137,137,118,23,118,118],160),([55,55,55,55,172,172,37,37,37,137,137,118,23,118,118],704),([144,144,144,144,172,172,37,37,37,137,137,118,23,118,118],738),([187,187,187,187,172,172,37,37,37,137,137,118,23,118,118],756),([100,100,100,217,217,217,37,37,37,137,137,118,23,118,118],1292),([232,232,232,217,217,217,37,37,37,137,137,118,23,118,118],1328),([55,55,55,55,40,104,104,104,104,137,137,118,23,118,118],14),([144,144,144,144,40,104,104,104,104,137,137,118,23,118,118],48),([187,187,187,187,40,104,104,104,104,137,137,118,23,118,118],66),([55,55,55,55,107,104,104,104,104,137,137,118,23,118,118],338),([144,144,144,144,107,104,104,104,104,137,137,118,23,118,118],490),([187,187,187,187,107,104,104,104,104,137,137,118,23,118,118],562),([55,55,55,55,194,104,104,104,104,137,137,118,23,118,118],934),([144,144,144,144,194,104,104,104,104,137,137,118,23,118,118],1086),([187,187,187,187,194,104,104,104,104,137,137,118,23,118,118],1158),([55,55,55,55,239,104,104,104,104,137,137,118,23,118,118],1414),([144,144,144,144,239,104,104,104,104,137,137,118,23,118,118],1566),([187,187,187,187,239,104,104,104,104,137,137,118,23,118,118],1638),([55,55,55,55,85,85,168,168,168,137,137,118,23,118,118],202),([144,144,144,144,85,85,168,168,168,137,137,118,23,118,118],236),([187,187,187,187,85,85,168,168,168,137,137,118,23,118,118],254),([55,55,55,55,172,172,168,168,168,137,137,118,23,118,118],798)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H4_part0 : ((probeRowWitnessesT8H4.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H4_part1 : ((probeRowWitnessesT8H4.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H4_part2 : ((probeRowWitnessesT8H4.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H4_part3 : ((probeRowWitnessesT8H4.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H4_checked : probeRowWitnessesT8H4.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H4.drop 0).take 8 ++ (probeRowWitnessesT8H4.drop 8).take 8 ++ (probeRowWitnessesT8H4.drop 16).take 8 ++ (probeRowWitnessesT8H4.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H4_part0,probeRowWitnessesT8H4_part1,probeRowWitnessesT8H4_part2,probeRowWitnessesT8H4_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
