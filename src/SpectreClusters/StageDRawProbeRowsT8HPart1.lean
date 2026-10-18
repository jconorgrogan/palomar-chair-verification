module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H1 : List (List Nat × Nat) := [([123,123,228,123,194,148,148,148,30,228,114,114,114,30,30],1027),([256,256,228,256,194,148,148,148,30,228,114,114,114,30,30],1251),([123,123,228,123,239,148,148,148,30,228,114,114,114,30,30],1507),([256,256,228,256,239,148,148,148,30,228,114,114,114,30,30],1731),([123,123,28,123,107,16,16,16,30,28,28,177,177,30,30],414),([256,256,28,256,107,16,16,16,30,28,28,177,177,30,30],638),([123,123,28,123,194,16,16,16,30,28,28,177,177,30,30],1010),([256,256,28,256,194,16,16,16,30,28,28,177,177,30,30],1234),([123,123,28,123,239,16,16,16,30,28,28,177,177,30,30],1490),([256,256,28,256,239,16,16,16,30,28,28,177,177,30,30],1714),([123,123,28,123,107,148,148,148,30,28,28,177,177,30,30],415),([256,256,28,256,107,148,148,148,30,28,28,177,177,30,30],639),([123,123,28,123,194,148,148,148,30,28,28,177,177,30,30],1011),([256,256,28,256,194,148,148,148,30,28,28,177,177,30,30],1235),([123,123,28,123,239,148,148,148,30,28,28,177,177,30,30],1491),([256,256,28,256,239,148,148,148,30,28,28,177,177,30,30],1715),([123,123,28,123,85,85,37,37,37,28,28,118,23,118,118],120),([256,256,28,256,85,85,37,37,37,28,28,118,23,118,118],172),([123,123,28,123,172,172,37,37,37,28,28,118,23,118,118],716),([256,256,28,256,172,172,37,37,37,28,28,118,23,118,118],768),([123,123,28,123,40,104,104,104,104,28,28,118,23,118,118],26),([256,256,28,256,40,104,104,104,104,28,28,118,23,118,118],78),([123,123,28,123,107,104,104,104,104,28,28,118,23,118,118],386),([256,256,28,256,107,104,104,104,104,28,28,118,23,118,118],610),([123,123,28,123,194,104,104,104,104,28,28,118,23,118,118],982),([256,256,28,256,194,104,104,104,104,28,28,118,23,118,118],1206),([123,123,28,123,239,104,104,104,104,28,28,118,23,118,118],1462),([256,256,28,256,239,104,104,104,104,28,28,118,23,118,118],1686),([123,123,28,123,85,85,168,168,168,28,28,118,23,118,118],214),([256,256,28,256,85,85,168,168,168,28,28,118,23,118,118],266),([123,123,28,123,172,172,168,168,168,28,28,118,23,118,118],810),([256,256,28,256,172,172,168,168,168,28,28,118,23,118,118],862)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H1_part0 : ((probeRowWitnessesT8H1.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H1_part1 : ((probeRowWitnessesT8H1.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H1_part2 : ((probeRowWitnessesT8H1.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H1_part3 : ((probeRowWitnessesT8H1.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H1_checked : probeRowWitnessesT8H1.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H1.drop 0).take 8 ++ (probeRowWitnessesT8H1.drop 8).take 8 ++ (probeRowWitnessesT8H1.drop 16).take 8 ++ (probeRowWitnessesT8H1.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H1_part0,probeRowWitnessesT8H1_part1,probeRowWitnessesT8H1_part2,probeRowWitnessesT8H1_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
