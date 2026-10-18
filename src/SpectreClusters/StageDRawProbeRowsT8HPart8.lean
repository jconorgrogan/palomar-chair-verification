module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H8 : List (List Nat × Nat) := [([123,123,28,123,85,85,37,37,37,28,28,118,90,118,118],122),([256,256,28,256,85,85,37,37,37,28,28,118,90,118,118],174),([123,123,28,123,172,172,37,37,37,28,28,118,90,118,118],718),([256,256,28,256,172,172,37,37,37,28,28,118,90,118,118],770),([123,123,28,123,40,104,104,104,104,28,28,118,90,118,118],28),([256,256,28,256,40,104,104,104,104,28,28,118,90,118,118],80),([123,123,28,123,107,104,104,104,104,28,28,118,90,118,118],398),([256,256,28,256,107,104,104,104,104,28,28,118,90,118,118],622),([123,123,28,123,194,104,104,104,104,28,28,118,90,118,118],994),([256,256,28,256,194,104,104,104,104,28,28,118,90,118,118],1218),([123,123,28,123,239,104,104,104,104,28,28,118,90,118,118],1474),([256,256,28,256,239,104,104,104,104,28,28,118,90,118,118],1698),([123,123,28,123,85,85,168,168,168,28,28,118,90,118,118],216),([256,256,28,256,85,85,168,168,168,28,28,118,90,118,118],268),([123,123,28,123,172,172,168,168,168,28,28,118,90,118,118],812),([256,256,28,256,172,172,168,168,168,28,28,118,90,118,118],864),([123,123,28,123,107,191,191,191,191,28,28,118,90,118,118],399),([256,256,28,256,107,191,191,191,191,28,28,118,90,118,118],623),([123,123,28,123,194,191,191,191,191,28,28,118,90,118,118],995),([256,256,28,256,194,191,191,191,191,28,28,118,90,118,118],1219),([123,123,28,123,239,191,191,191,191,28,28,118,90,118,118],1475),([256,256,28,256,239,191,191,191,191,28,28,118,90,118,118],1699),([123,123,28,123,107,236,236,236,236,28,28,118,90,118,118],400),([256,256,28,256,107,236,236,236,236,28,28,118,90,118,118],624),([123,123,28,123,194,236,236,236,236,28,28,118,90,118,118],996),([256,256,28,256,194,236,236,236,236,28,28,118,90,118,118],1220),([123,123,28,123,239,236,236,236,236,28,28,118,90,118,118],1476),([256,256,28,256,239,236,236,236,236,28,28,118,90,118,118],1700),([55,55,55,55,85,85,37,37,37,116,116,118,90,118,118],102),([55,55,55,55,172,172,37,37,37,116,116,118,90,118,118],698),([55,55,55,55,40,104,104,104,104,116,116,118,90,118,118],8),([55,55,55,55,107,104,104,104,104,116,116,118,90,118,118],314)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H8_part0 : ((probeRowWitnessesT8H8.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H8_part1 : ((probeRowWitnessesT8H8.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H8_part2 : ((probeRowWitnessesT8H8.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H8_part3 : ((probeRowWitnessesT8H8.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H8_checked : probeRowWitnessesT8H8.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H8.drop 0).take 8 ++ (probeRowWitnessesT8H8.drop 8).take 8 ++ (probeRowWitnessesT8H8.drop 16).take 8 ++ (probeRowWitnessesT8H8.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H8_part0,probeRowWitnessesT8H8_part1,probeRowWitnessesT8H8_part2,probeRowWitnessesT8H8_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
