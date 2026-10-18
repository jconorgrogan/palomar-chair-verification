module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT7H1 : List (List Nat × Nat) := [([241,135,229,258,49,35],32),([23,177,229,258,49,35],33),([153,177,229,258,49,35],34),([241,177,229,258,49,35],35),([23,47,98,126,179,35],36),([153,47,98,126,179,35],37),([241,47,98,126,179,35],38),([23,135,98,126,179,35],39),([153,135,98,126,179,35],40),([241,135,98,126,179,35],41),([23,177,98,126,179,35],42),([153,177,98,126,179,35],43),([241,177,98,126,179,35],44),([23,47,229,126,179,35],45),([153,47,229,126,179,35],46),([241,47,229,126,179,35],47),([23,135,229,126,179,35],48),([153,135,229,126,179,35],49),([241,135,229,126,179,35],50),([23,177,229,126,179,35],51),([153,177,229,126,179,35],52),([241,177,229,126,179,35],53),([23,47,98,258,179,35],54),([153,47,98,258,179,35],55),([241,47,98,258,179,35],56),([23,135,98,258,179,35],57),([153,135,98,258,179,35],58),([241,135,98,258,179,35],59),([23,177,98,258,179,35],60),([153,177,98,258,179,35],61),([241,177,98,258,179,35],62),([23,47,229,258,179,35],63)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H1_part0 : ((probeRowWitnessesT7H1.drop 0).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H1_part1 : ((probeRowWitnessesT7H1.drop 8).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H1_part2 : ((probeRowWitnessesT7H1.drop 16).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H1_part3 : ((probeRowWitnessesT7H1.drop 24).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H1_checked : probeRowWitnessesT7H1.all (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT7H1.drop 0).take 8 ++ (probeRowWitnessesT7H1.drop 8).take 8 ++ (probeRowWitnessesT7H1.drop 16).take 8 ++ (probeRowWitnessesT7H1.drop 24).take 8).all (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT7H1_part0,probeRowWitnessesT7H1_part1,probeRowWitnessesT7H1_part2,probeRowWitnessesT7H1_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
