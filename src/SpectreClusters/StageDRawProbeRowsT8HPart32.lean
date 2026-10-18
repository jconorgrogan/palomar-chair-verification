module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H32 : List (List Nat × Nat) := [([123,123,28,123,239,236,236,236,236,28,28,206,90,206,206],1479),([256,256,28,256,239,236,236,236,236,28,28,206,90,206,206],1703),([55,55,55,55,85,85,37,37,37,116,116,206,90,206,206],103),([55,55,55,55,172,172,37,37,37,116,116,206,90,206,206],699),([55,55,55,55,40,104,104,104,104,116,116,206,90,206,206],9),([55,55,55,55,107,104,104,104,104,116,116,206,90,206,206],317),([55,55,55,55,194,104,104,104,104,116,116,206,90,206,206],913),([55,55,55,55,239,104,104,104,104,116,116,206,90,206,206],1393),([55,55,55,55,85,85,168,168,168,116,116,206,90,206,206],197),([55,55,55,55,172,172,168,168,168,116,116,206,90,206,206],793),([55,55,55,55,107,191,191,191,191,116,116,206,90,206,206],318),([55,55,55,55,194,191,191,191,191,116,116,206,90,206,206],914),([55,55,55,55,239,191,191,191,191,116,116,206,90,206,206],1394),([55,55,55,55,107,236,236,236,236,116,116,206,90,206,206],319),([55,55,55,55,194,236,236,236,236,116,116,206,90,206,206],915),([55,55,55,55,239,236,236,236,236,116,116,206,90,206,206],1395),([123,123,249,123,85,85,37,37,37,249,249,206,90,206,206],131),([256,256,249,256,85,85,37,37,37,249,249,206,90,206,206],183),([123,123,249,123,172,172,37,37,37,249,249,206,90,206,206],727),([256,256,249,256,172,172,37,37,37,249,249,206,90,206,206],779),([123,123,249,123,40,104,104,104,104,249,249,206,90,206,206],37),([256,256,249,256,40,104,104,104,104,249,249,206,90,206,206],89),([123,123,249,123,107,104,104,104,104,249,249,206,90,206,206],445),([256,256,249,256,107,104,104,104,104,249,249,206,90,206,206],669),([123,123,249,123,194,104,104,104,104,249,249,206,90,206,206],1041),([256,256,249,256,194,104,104,104,104,249,249,206,90,206,206],1265),([123,123,249,123,239,104,104,104,104,249,249,206,90,206,206],1521),([256,256,249,256,239,104,104,104,104,249,249,206,90,206,206],1745),([123,123,249,123,85,85,168,168,168,249,249,206,90,206,206],225),([256,256,249,256,85,85,168,168,168,249,249,206,90,206,206],277),([123,123,249,123,172,172,168,168,168,249,249,206,90,206,206],821),([256,256,249,256,172,172,168,168,168,249,249,206,90,206,206],873)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H32_part0 : ((probeRowWitnessesT8H32.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H32_part1 : ((probeRowWitnessesT8H32.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H32_part2 : ((probeRowWitnessesT8H32.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H32_part3 : ((probeRowWitnessesT8H32.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H32_checked : probeRowWitnessesT8H32.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H32.drop 0).take 8 ++ (probeRowWitnessesT8H32.drop 8).take 8 ++ (probeRowWitnessesT8H32.drop 16).take 8 ++ (probeRowWitnessesT8H32.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H32_part0,probeRowWitnessesT8H32_part1,probeRowWitnessesT8H32_part2,probeRowWitnessesT8H32_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
