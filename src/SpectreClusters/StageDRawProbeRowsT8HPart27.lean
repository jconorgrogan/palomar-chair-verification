module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H27 : List (List Nat × Nat) := [([55,55,55,55,85,85,37,37,37,116,116,206,23,206,206],101),([55,55,55,55,172,172,37,37,37,116,116,206,23,206,206],697),([55,55,55,55,40,104,104,104,104,116,116,206,23,206,206],7),([55,55,55,55,107,104,104,104,104,116,116,206,23,206,206],309),([55,55,55,55,194,104,104,104,104,116,116,206,23,206,206],905),([55,55,55,55,239,104,104,104,104,116,116,206,23,206,206],1385),([55,55,55,55,85,85,168,168,168,116,116,206,23,206,206],195),([55,55,55,55,172,172,168,168,168,116,116,206,23,206,206],791),([55,55,55,55,107,191,191,191,191,116,116,206,23,206,206],310),([55,55,55,55,194,191,191,191,191,116,116,206,23,206,206],906),([55,55,55,55,239,191,191,191,191,116,116,206,23,206,206],1386),([55,55,55,55,107,236,236,236,236,116,116,206,23,206,206],311),([55,55,55,55,194,236,236,236,236,116,116,206,23,206,206],907),([55,55,55,55,239,236,236,236,236,116,116,206,23,206,206],1387),([55,55,55,55,85,85,37,37,37,137,137,206,23,206,206],109),([144,144,144,144,85,85,37,37,37,137,137,206,23,206,206],143),([187,187,187,187,85,85,37,37,37,137,137,206,23,206,206],161),([55,55,55,55,172,172,37,37,37,137,137,206,23,206,206],705),([144,144,144,144,172,172,37,37,37,137,137,206,23,206,206],739),([187,187,187,187,172,172,37,37,37,137,137,206,23,206,206],757),([100,100,100,217,217,217,37,37,37,137,137,206,23,206,206],1293),([232,232,232,217,217,217,37,37,37,137,137,206,23,206,206],1329),([55,55,55,55,40,104,104,104,104,137,137,206,23,206,206],15),([144,144,144,144,40,104,104,104,104,137,137,206,23,206,206],49),([187,187,187,187,40,104,104,104,104,137,137,206,23,206,206],67),([55,55,55,55,107,104,104,104,104,137,137,206,23,206,206],341),([144,144,144,144,107,104,104,104,104,137,137,206,23,206,206],493),([187,187,187,187,107,104,104,104,104,137,137,206,23,206,206],565),([55,55,55,55,194,104,104,104,104,137,137,206,23,206,206],937),([144,144,144,144,194,104,104,104,104,137,137,206,23,206,206],1089),([187,187,187,187,194,104,104,104,104,137,137,206,23,206,206],1161),([55,55,55,55,239,104,104,104,104,137,137,206,23,206,206],1417)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H27_part0 : ((probeRowWitnessesT8H27.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H27_part1 : ((probeRowWitnessesT8H27.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H27_part2 : ((probeRowWitnessesT8H27.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H27_part3 : ((probeRowWitnessesT8H27.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H27_checked : probeRowWitnessesT8H27.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H27.drop 0).take 8 ++ (probeRowWitnessesT8H27.drop 8).take 8 ++ (probeRowWitnessesT8H27.drop 16).take 8 ++ (probeRowWitnessesT8H27.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H27_part0,probeRowWitnessesT8H27_part1,probeRowWitnessesT8H27_part2,probeRowWitnessesT8H27_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
