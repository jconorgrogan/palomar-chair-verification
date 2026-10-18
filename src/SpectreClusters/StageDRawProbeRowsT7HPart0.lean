module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT7H0 : List (List Nat × Nat) := [([23,47,98,126,49,35],0),([153,47,98,126,49,35],1),([241,47,98,126,49,35],2),([23,135,98,126,49,35],3),([153,135,98,126,49,35],4),([241,135,98,126,49,35],5),([23,177,98,126,49,35],6),([153,177,98,126,49,35],7),([241,177,98,126,49,35],8),([23,47,229,126,49,35],9),([153,47,229,126,49,35],10),([241,47,229,126,49,35],11),([23,135,229,126,49,35],12),([153,135,229,126,49,35],13),([241,135,229,126,49,35],14),([23,177,229,126,49,35],15),([153,177,229,126,49,35],16),([241,177,229,126,49,35],17),([23,47,98,258,49,35],18),([153,47,98,258,49,35],19),([241,47,98,258,49,35],20),([23,135,98,258,49,35],21),([153,135,98,258,49,35],22),([241,135,98,258,49,35],23),([23,177,98,258,49,35],24),([153,177,98,258,49,35],25),([241,177,98,258,49,35],26),([23,47,229,258,49,35],27),([153,47,229,258,49,35],28),([241,47,229,258,49,35],29),([23,135,229,258,49,35],30),([153,135,229,258,49,35],31)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H0_part0 : ((probeRowWitnessesT7H0.drop 0).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H0_part1 : ((probeRowWitnessesT7H0.drop 8).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H0_part2 : ((probeRowWitnessesT7H0.drop 16).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H0_part3 : ((probeRowWitnessesT7H0.drop 24).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H0_checked : probeRowWitnessesT7H0.all (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT7H0.drop 0).take 8 ++ (probeRowWitnessesT7H0.drop 8).take 8 ++ (probeRowWitnessesT7H0.drop 16).take 8 ++ (probeRowWitnessesT7H0.drop 24).take 8).all (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT7H0_part0,probeRowWitnessesT7H0_part1,probeRowWitnessesT7H0_part2,probeRowWitnessesT7H0_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
