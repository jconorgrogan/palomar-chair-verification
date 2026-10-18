module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H34 : List (List Nat × Nat) := [([123,123,28,123,239,191,191,191,191,28,28,206,155,206,206],1486),([256,256,28,256,239,191,191,191,191,28,28,206,155,206,206],1710),([123,123,28,123,107,236,236,236,236,28,28,206,155,206,206],411),([256,256,28,256,107,236,236,236,236,28,28,206,155,206,206],635),([123,123,28,123,194,236,236,236,236,28,28,206,155,206,206],1007),([256,256,28,256,194,236,236,236,236,28,28,206,155,206,206],1231),([123,123,28,123,239,236,236,236,236,28,28,206,155,206,206],1487),([256,256,28,256,239,236,236,236,236,28,28,206,155,206,206],1711),([55,55,55,55,85,85,37,37,37,48,48,206,155,206,206],97),([144,144,144,144,85,85,37,37,37,48,48,206,155,206,206],139),([187,187,187,187,85,85,37,37,37,48,48,206,155,206,206],157),([55,55,55,55,172,172,37,37,37,48,48,206,155,206,206],693),([144,144,144,144,172,172,37,37,37,48,48,206,155,206,206],735),([187,187,187,187,172,172,37,37,37,48,48,206,155,206,206],753),([100,100,100,217,217,217,37,37,37,48,48,206,155,206,206],1289),([232,232,232,217,217,217,37,37,37,48,48,206,155,206,206],1325),([55,55,55,55,40,104,104,104,104,48,48,206,155,206,206],3),([144,144,144,144,40,104,104,104,104,48,48,206,155,206,206],45),([187,187,187,187,40,104,104,104,104,48,48,206,155,206,206],63),([55,55,55,55,107,104,104,104,104,48,48,206,155,206,206],293),([144,144,144,144,107,104,104,104,104,48,48,206,155,206,206],477),([187,187,187,187,107,104,104,104,104,48,48,206,155,206,206],549),([55,55,55,55,194,104,104,104,104,48,48,206,155,206,206],889),([144,144,144,144,194,104,104,104,104,48,48,206,155,206,206],1073),([187,187,187,187,194,104,104,104,104,48,48,206,155,206,206],1145),([55,55,55,55,239,104,104,104,104,48,48,206,155,206,206],1369),([144,144,144,144,239,104,104,104,104,48,48,206,155,206,206],1553),([187,187,187,187,239,104,104,104,104,48,48,206,155,206,206],1625),([55,55,55,55,85,85,168,168,168,48,48,206,155,206,206],191),([144,144,144,144,85,85,168,168,168,48,48,206,155,206,206],233),([187,187,187,187,85,85,168,168,168,48,48,206,155,206,206],251),([55,55,55,55,172,172,168,168,168,48,48,206,155,206,206],787)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H34_part0 : ((probeRowWitnessesT8H34.drop 0).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H34_part1 : ((probeRowWitnessesT8H34.drop 8).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H34_part2 : ((probeRowWitnessesT8H34.drop 16).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H34_part3 : ((probeRowWitnessesT8H34.drop 24).take 8).all
    (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H34_checked : probeRowWitnessesT8H34.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT8H34.drop 0).take 8 ++ (probeRowWitnessesT8H34.drop 8).take 8 ++ (probeRowWitnessesT8H34.drop 16).take 8 ++ (probeRowWitnessesT8H34.drop 24).take 8).all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT8H34_part0,probeRowWitnessesT8H34_part1,probeRowWitnessesT8H34_part2,probeRowWitnessesT8H34_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
