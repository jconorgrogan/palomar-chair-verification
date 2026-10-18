module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H47 : List (List Nat × Nat) := [([187,187,187,187,239,16,16,16,251,48,48,251,23,251,251],1620),([55,55,55,55,107,148,148,148,251,48,48,251,23,251,251],289),([144,144,144,144,107,148,148,148,251,48,48,251,23,251,251],473),([187,187,187,187,107,148,148,148,251,48,48,251,23,251,251],545),([55,55,55,55,194,148,148,148,251,48,48,251,23,251,251],885),([144,144,144,144,194,148,148,148,251,48,48,251,23,251,251],1069),([187,187,187,187,194,148,148,148,251,48,48,251,23,251,251],1141),([55,55,55,55,239,148,148,148,251,48,48,251,23,251,251],1365),([144,144,144,144,239,148,148,148,251,48,48,251,23,251,251],1549),([187,187,187,187,239,148,148,148,251,48,48,251,23,251,251],1621),([55,55,55,55,107,16,16,16,251,116,116,251,23,251,251],312),([55,55,55,55,194,16,16,16,251,116,116,251,23,251,251],908),([55,55,55,55,239,16,16,16,251,116,116,251,23,251,251],1388),([55,55,55,55,107,148,148,148,251,116,116,251,23,251,251],313),([55,55,55,55,194,148,148,148,251,116,116,251,23,251,251],909),([55,55,55,55,239,148,148,148,251,116,116,251,23,251,251],1389),([55,55,55,55,107,16,16,16,251,137,137,251,23,251,251],344),([144,144,144,144,107,16,16,16,251,137,137,251,23,251,251],496),([187,187,187,187,107,16,16,16,251,137,137,251,23,251,251],568),([55,55,55,55,194,16,16,16,251,137,137,251,23,251,251],940),([144,144,144,144,194,16,16,16,251,137,137,251,23,251,251],1092),([187,187,187,187,194,16,16,16,251,137,137,251,23,251,251],1164),([55,55,55,55,239,16,16,16,251,137,137,251,23,251,251],1420),([144,144,144,144,239,16,16,16,251,137,137,251,23,251,251],1572),([187,187,187,187,239,16,16,16,251,137,137,251,23,251,251],1644),([55,55,55,55,107,148,148,148,251,137,137,251,23,251,251],345),([144,144,144,144,107,148,148,148,251,137,137,251,23,251,251],497),([187,187,187,187,107,148,148,148,251,137,137,251,23,251,251],569),([55,55,55,55,194,148,148,148,251,137,137,251,23,251,251],941),([144,144,144,144,194,148,148,148,251,137,137,251,23,251,251],1093),([187,187,187,187,194,148,148,148,251,137,137,251,23,251,251],1165),([55,55,55,55,239,148,148,148,251,137,137,251,23,251,251],1421)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H47_part0 : ((probeRowWitnessesT8H47.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H47_part1 : ((probeRowWitnessesT8H47.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H47_part2 : ((probeRowWitnessesT8H47.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H47_part3 : ((probeRowWitnessesT8H47.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H47_checked : probeRowWitnessesT8H47.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H47.drop 0).take 8 ++ (probeRowWitnessesT8H47.drop 8).take 8 ++ (probeRowWitnessesT8H47.drop 16).take 8 ++ (probeRowWitnessesT8H47.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H47_part0,probeRowWitnessesT8H47_part1,probeRowWitnessesT8H47_part2,probeRowWitnessesT8H47_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
