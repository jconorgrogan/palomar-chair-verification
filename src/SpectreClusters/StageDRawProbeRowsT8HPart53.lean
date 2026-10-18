module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H53 : List (List Nat × Nat) := [([187,187,187,187,107,16,16,16,251,48,48,251,244,251,251],560),([55,55,55,55,194,16,16,16,251,48,48,251,244,251,251],900),([144,144,144,144,194,16,16,16,251,48,48,251,244,251,251],1084),([187,187,187,187,194,16,16,16,251,48,48,251,244,251,251],1156),([55,55,55,55,239,16,16,16,251,48,48,251,244,251,251],1380),([144,144,144,144,239,16,16,16,251,48,48,251,244,251,251],1564),([187,187,187,187,239,16,16,16,251,48,48,251,244,251,251],1636),([55,55,55,55,107,148,148,148,251,48,48,251,244,251,251],305),([144,144,144,144,107,148,148,148,251,48,48,251,244,251,251],489),([187,187,187,187,107,148,148,148,251,48,48,251,244,251,251],561),([55,55,55,55,194,148,148,148,251,48,48,251,244,251,251],901),([144,144,144,144,194,148,148,148,251,48,48,251,244,251,251],1085),([187,187,187,187,194,148,148,148,251,48,48,251,244,251,251],1157),([55,55,55,55,239,148,148,148,251,48,48,251,244,251,251],1381),([144,144,144,144,239,148,148,148,251,48,48,251,244,251,251],1565),([187,187,187,187,239,148,148,148,251,48,48,251,244,251,251],1637),([55,55,55,55,107,16,16,16,251,116,116,251,244,251,251],336),([55,55,55,55,194,16,16,16,251,116,116,251,244,251,251],932),([55,55,55,55,239,16,16,16,251,116,116,251,244,251,251],1412),([55,55,55,55,107,148,148,148,251,116,116,251,244,251,251],337),([55,55,55,55,194,148,148,148,251,116,116,251,244,251,251],933),([55,55,55,55,239,148,148,148,251,116,116,251,244,251,251],1413),([55,55,55,55,107,16,16,16,251,137,137,251,244,251,251],360),([144,144,144,144,107,16,16,16,251,137,137,251,244,251,251],512),([187,187,187,187,107,16,16,16,251,137,137,251,244,251,251],584),([55,55,55,55,194,16,16,16,251,137,137,251,244,251,251],956),([144,144,144,144,194,16,16,16,251,137,137,251,244,251,251],1108),([187,187,187,187,194,16,16,16,251,137,137,251,244,251,251],1180),([55,55,55,55,239,16,16,16,251,137,137,251,244,251,251],1436),([144,144,144,144,239,16,16,16,251,137,137,251,244,251,251],1588),([187,187,187,187,239,16,16,16,251,137,137,251,244,251,251],1660),([55,55,55,55,107,148,148,148,251,137,137,251,244,251,251],361)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H53_part0 : ((probeRowWitnessesT8H53.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H53_part1 : ((probeRowWitnessesT8H53.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H53_part2 : ((probeRowWitnessesT8H53.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H53_part3 : ((probeRowWitnessesT8H53.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H53_checked : probeRowWitnessesT8H53.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H53.drop 0).take 8 ++ (probeRowWitnessesT8H53.drop 8).take 8 ++ (probeRowWitnessesT8H53.drop 16).take 8 ++ (probeRowWitnessesT8H53.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H53_part0,probeRowWitnessesT8H53_part1,probeRowWitnessesT8H53_part2,probeRowWitnessesT8H53_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
