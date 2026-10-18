module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H49 : List (List Nat × Nat) := [([123,123,28,123,107,16,16,16,251,28,28,251,90,251,251],404),([256,256,28,256,107,16,16,16,251,28,28,251,90,251,251],628),([123,123,28,123,194,16,16,16,251,28,28,251,90,251,251],1000),([256,256,28,256,194,16,16,16,251,28,28,251,90,251,251],1224),([123,123,28,123,239,16,16,16,251,28,28,251,90,251,251],1480),([256,256,28,256,239,16,16,16,251,28,28,251,90,251,251],1704),([123,123,28,123,107,148,148,148,251,28,28,251,90,251,251],405),([256,256,28,256,107,148,148,148,251,28,28,251,90,251,251],629),([123,123,28,123,194,148,148,148,251,28,28,251,90,251,251],1001),([256,256,28,256,194,148,148,148,251,28,28,251,90,251,251],1225),([123,123,28,123,239,148,148,148,251,28,28,251,90,251,251],1481),([256,256,28,256,239,148,148,148,251,28,28,251,90,251,251],1705),([55,55,55,55,107,16,16,16,251,116,116,251,90,251,251],320),([55,55,55,55,194,16,16,16,251,116,116,251,90,251,251],916),([55,55,55,55,239,16,16,16,251,116,116,251,90,251,251],1396),([55,55,55,55,107,148,148,148,251,116,116,251,90,251,251],321),([55,55,55,55,194,148,148,148,251,116,116,251,90,251,251],917),([55,55,55,55,239,148,148,148,251,116,116,251,90,251,251],1397),([123,123,249,123,107,16,16,16,251,249,249,251,90,251,251],448),([256,256,249,256,107,16,16,16,251,249,249,251,90,251,251],672),([123,123,249,123,194,16,16,16,251,249,249,251,90,251,251],1044),([256,256,249,256,194,16,16,16,251,249,249,251,90,251,251],1268),([123,123,249,123,239,16,16,16,251,249,249,251,90,251,251],1524),([256,256,249,256,239,16,16,16,251,249,249,251,90,251,251],1748),([123,123,249,123,107,148,148,148,251,249,249,251,90,251,251],449),([256,256,249,256,107,148,148,148,251,249,249,251,90,251,251],673),([123,123,249,123,194,148,148,148,251,249,249,251,90,251,251],1045),([256,256,249,256,194,148,148,148,251,249,249,251,90,251,251],1269),([123,123,249,123,239,148,148,148,251,249,249,251,90,251,251],1525),([256,256,249,256,239,148,148,148,251,249,249,251,90,251,251],1749),([123,123,28,123,107,16,16,16,251,28,28,251,155,251,251],412),([256,256,28,256,107,16,16,16,251,28,28,251,155,251,251],636)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H49_part0 : ((probeRowWitnessesT8H49.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H49_part1 : ((probeRowWitnessesT8H49.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H49_part2 : ((probeRowWitnessesT8H49.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H49_part3 : ((probeRowWitnessesT8H49.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H49_checked : probeRowWitnessesT8H49.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H49.drop 0).take 8 ++ (probeRowWitnessesT8H49.drop 8).take 8 ++ (probeRowWitnessesT8H49.drop 16).take 8 ++ (probeRowWitnessesT8H49.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H49_part0,probeRowWitnessesT8H49_part1,probeRowWitnessesT8H49_part2,probeRowWitnessesT8H49_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
