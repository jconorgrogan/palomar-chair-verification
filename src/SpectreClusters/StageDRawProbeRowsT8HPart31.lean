module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H31 : List (List Nat × Nat) := [([123,123,249,123,107,236,236,236,236,249,249,206,23,206,206],439),([256,256,249,256,107,236,236,236,236,249,249,206,23,206,206],663),([123,123,249,123,194,236,236,236,236,249,249,206,23,206,206],1035),([256,256,249,256,194,236,236,236,236,249,249,206,23,206,206],1259),([123,123,249,123,239,236,236,236,236,249,249,206,23,206,206],1515),([256,256,249,256,239,236,236,236,236,249,249,206,23,206,206],1739),([123,123,28,123,85,85,37,37,37,28,28,206,90,206,206],130),([256,256,28,256,85,85,37,37,37,28,28,206,90,206,206],182),([123,123,28,123,172,172,37,37,37,28,28,206,90,206,206],726),([256,256,28,256,172,172,37,37,37,28,28,206,90,206,206],778),([123,123,28,123,40,104,104,104,104,28,28,206,90,206,206],36),([256,256,28,256,40,104,104,104,104,28,28,206,90,206,206],88),([123,123,28,123,107,104,104,104,104,28,28,206,90,206,206],401),([256,256,28,256,107,104,104,104,104,28,28,206,90,206,206],625),([123,123,28,123,194,104,104,104,104,28,28,206,90,206,206],997),([256,256,28,256,194,104,104,104,104,28,28,206,90,206,206],1221),([123,123,28,123,239,104,104,104,104,28,28,206,90,206,206],1477),([256,256,28,256,239,104,104,104,104,28,28,206,90,206,206],1701),([123,123,28,123,85,85,168,168,168,28,28,206,90,206,206],224),([256,256,28,256,85,85,168,168,168,28,28,206,90,206,206],276),([123,123,28,123,172,172,168,168,168,28,28,206,90,206,206],820),([256,256,28,256,172,172,168,168,168,28,28,206,90,206,206],872),([123,123,28,123,107,191,191,191,191,28,28,206,90,206,206],402),([256,256,28,256,107,191,191,191,191,28,28,206,90,206,206],626),([123,123,28,123,194,191,191,191,191,28,28,206,90,206,206],998),([256,256,28,256,194,191,191,191,191,28,28,206,90,206,206],1222),([123,123,28,123,239,191,191,191,191,28,28,206,90,206,206],1478),([256,256,28,256,239,191,191,191,191,28,28,206,90,206,206],1702),([123,123,28,123,107,236,236,236,236,28,28,206,90,206,206],403),([256,256,28,256,107,236,236,236,236,28,28,206,90,206,206],627),([123,123,28,123,194,236,236,236,236,28,28,206,90,206,206],999),([256,256,28,256,194,236,236,236,236,28,28,206,90,206,206],1223)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H31_part0 : ((probeRowWitnessesT8H31.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H31_part1 : ((probeRowWitnessesT8H31.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H31_part2 : ((probeRowWitnessesT8H31.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H31_part3 : ((probeRowWitnessesT8H31.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H31_checked : probeRowWitnessesT8H31.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H31.drop 0).take 8 ++ (probeRowWitnessesT8H31.drop 8).take 8 ++ (probeRowWitnessesT8H31.drop 16).take 8 ++ (probeRowWitnessesT8H31.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H31_part0,probeRowWitnessesT8H31_part1,probeRowWitnessesT8H31_part2,probeRowWitnessesT8H31_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
