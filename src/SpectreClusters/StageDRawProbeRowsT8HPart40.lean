module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H40 : List (List Nat × Nat) := [([123,123,28,123,40,104,104,104,104,28,28,206,244,206,206],40),([256,256,28,256,40,104,104,104,104,28,28,206,244,206,206],92),([123,123,28,123,107,104,104,104,104,28,28,206,244,206,206],421),([256,256,28,256,107,104,104,104,104,28,28,206,244,206,206],645),([123,123,28,123,194,104,104,104,104,28,28,206,244,206,206],1017),([256,256,28,256,194,104,104,104,104,28,28,206,244,206,206],1241),([123,123,28,123,239,104,104,104,104,28,28,206,244,206,206],1497),([256,256,28,256,239,104,104,104,104,28,28,206,244,206,206],1721),([123,123,28,123,85,85,168,168,168,28,28,206,244,206,206],228),([256,256,28,256,85,85,168,168,168,28,28,206,244,206,206],280),([123,123,28,123,172,172,168,168,168,28,28,206,244,206,206],824),([256,256,28,256,172,172,168,168,168,28,28,206,244,206,206],876),([123,123,28,123,107,191,191,191,191,28,28,206,244,206,206],422),([256,256,28,256,107,191,191,191,191,28,28,206,244,206,206],646),([123,123,28,123,194,191,191,191,191,28,28,206,244,206,206],1018),([256,256,28,256,194,191,191,191,191,28,28,206,244,206,206],1242),([123,123,28,123,239,191,191,191,191,28,28,206,244,206,206],1498),([256,256,28,256,239,191,191,191,191,28,28,206,244,206,206],1722),([123,123,28,123,107,236,236,236,236,28,28,206,244,206,206],423),([256,256,28,256,107,236,236,236,236,28,28,206,244,206,206],647),([123,123,28,123,194,236,236,236,236,28,28,206,244,206,206],1019),([256,256,28,256,194,236,236,236,236,28,28,206,244,206,206],1243),([123,123,28,123,239,236,236,236,236,28,28,206,244,206,206],1499),([256,256,28,256,239,236,236,236,236,28,28,206,244,206,206],1723),([55,55,55,55,85,85,37,37,37,48,48,206,244,206,206],99),([144,144,144,144,85,85,37,37,37,48,48,206,244,206,206],141),([187,187,187,187,85,85,37,37,37,48,48,206,244,206,206],159),([55,55,55,55,172,172,37,37,37,48,48,206,244,206,206],695),([144,144,144,144,172,172,37,37,37,48,48,206,244,206,206],737),([187,187,187,187,172,172,37,37,37,48,48,206,244,206,206],755),([100,100,100,217,217,217,37,37,37,48,48,206,244,206,206],1291),([232,232,232,217,217,217,37,37,37,48,48,206,244,206,206],1327)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H40_part0 : ((probeRowWitnessesT8H40.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H40_part1 : ((probeRowWitnessesT8H40.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H40_part2 : ((probeRowWitnessesT8H40.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H40_part3 : ((probeRowWitnessesT8H40.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H40_checked : probeRowWitnessesT8H40.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H40.drop 0).take 8 ++ (probeRowWitnessesT8H40.drop 8).take 8 ++ (probeRowWitnessesT8H40.drop 16).take 8 ++ (probeRowWitnessesT8H40.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H40_part0,probeRowWitnessesT8H40_part1,probeRowWitnessesT8H40_part2,probeRowWitnessesT8H40_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
