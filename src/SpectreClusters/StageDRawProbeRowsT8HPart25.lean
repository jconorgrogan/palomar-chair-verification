module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H25 : List (List Nat × Nat) := [([123,123,28,123,239,104,104,104,104,28,28,206,23,206,206],1465),([256,256,28,256,239,104,104,104,104,28,28,206,23,206,206],1689),([123,123,28,123,85,85,168,168,168,28,28,206,23,206,206],222),([256,256,28,256,85,85,168,168,168,28,28,206,23,206,206],274),([123,123,28,123,172,172,168,168,168,28,28,206,23,206,206],818),([256,256,28,256,172,172,168,168,168,28,28,206,23,206,206],870),([123,123,28,123,107,191,191,191,191,28,28,206,23,206,206],390),([256,256,28,256,107,191,191,191,191,28,28,206,23,206,206],614),([123,123,28,123,194,191,191,191,191,28,28,206,23,206,206],986),([256,256,28,256,194,191,191,191,191,28,28,206,23,206,206],1210),([123,123,28,123,239,191,191,191,191,28,28,206,23,206,206],1466),([256,256,28,256,239,191,191,191,191,28,28,206,23,206,206],1690),([123,123,28,123,107,236,236,236,236,28,28,206,23,206,206],391),([256,256,28,256,107,236,236,236,236,28,28,206,23,206,206],615),([123,123,28,123,194,236,236,236,236,28,28,206,23,206,206],987),([256,256,28,256,194,236,236,236,236,28,28,206,23,206,206],1211),([123,123,28,123,239,236,236,236,236,28,28,206,23,206,206],1467),([256,256,28,256,239,236,236,236,236,28,28,206,23,206,206],1691),([55,55,55,55,85,85,37,37,37,48,48,206,23,206,206],95),([144,144,144,144,85,85,37,37,37,48,48,206,23,206,206],137),([187,187,187,187,85,85,37,37,37,48,48,206,23,206,206],155),([55,55,55,55,172,172,37,37,37,48,48,206,23,206,206],691),([144,144,144,144,172,172,37,37,37,48,48,206,23,206,206],733),([187,187,187,187,172,172,37,37,37,48,48,206,23,206,206],751),([100,100,100,217,217,217,37,37,37,48,48,206,23,206,206],1287),([232,232,232,217,217,217,37,37,37,48,48,206,23,206,206],1323),([55,55,55,55,40,104,104,104,104,48,48,206,23,206,206],1),([144,144,144,144,40,104,104,104,104,48,48,206,23,206,206],43),([187,187,187,187,40,104,104,104,104,48,48,206,23,206,206],61),([55,55,55,55,107,104,104,104,104,48,48,206,23,206,206],285),([144,144,144,144,107,104,104,104,104,48,48,206,23,206,206],469),([187,187,187,187,107,104,104,104,104,48,48,206,23,206,206],541)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H25_part0 : ((probeRowWitnessesT8H25.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H25_part1 : ((probeRowWitnessesT8H25.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H25_part2 : ((probeRowWitnessesT8H25.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H25_part3 : ((probeRowWitnessesT8H25.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H25_checked : probeRowWitnessesT8H25.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H25.drop 0).take 8 ++ (probeRowWitnessesT8H25.drop 8).take 8 ++ (probeRowWitnessesT8H25.drop 16).take 8 ++ (probeRowWitnessesT8H25.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H25_part0,probeRowWitnessesT8H25_part1,probeRowWitnessesT8H25_part2,probeRowWitnessesT8H25_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
