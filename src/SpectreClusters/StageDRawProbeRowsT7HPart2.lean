module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT7H2 : List (List Nat × Nat) := [([153,47,229,258,179,35],64),([241,47,229,258,179,35],65),([23,135,229,258,179,35],66),([153,135,229,258,179,35],67),([241,135,229,258,179,35],68),([23,177,229,258,179,35],69),([153,177,229,258,179,35],70),([241,177,229,258,179,35],71),([23,47,98,126,49,164],72),([153,47,98,126,49,164],73),([241,47,98,126,49,164],74),([23,135,98,126,49,164],75),([153,135,98,126,49,164],76),([241,135,98,126,49,164],77),([23,177,98,126,49,164],78),([153,177,98,126,49,164],79),([241,177,98,126,49,164],80),([23,47,229,126,49,164],81),([153,47,229,126,49,164],82),([241,47,229,126,49,164],83),([23,135,229,126,49,164],84),([153,135,229,126,49,164],85),([241,135,229,126,49,164],86),([23,177,229,126,49,164],87),([153,177,229,126,49,164],88),([241,177,229,126,49,164],89),([23,47,98,258,49,164],90),([153,47,98,258,49,164],91),([241,47,98,258,49,164],92),([23,135,98,258,49,164],93),([153,135,98,258,49,164],94),([241,135,98,258,49,164],95)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H2_part0 : ((probeRowWitnessesT7H2.drop 0).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H2_part1 : ((probeRowWitnessesT7H2.drop 8).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H2_part2 : ((probeRowWitnessesT7H2.drop 16).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H2_part3 : ((probeRowWitnessesT7H2.drop 24).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H2_checked : probeRowWitnessesT7H2.all (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT7H2.drop 0).take 8 ++ (probeRowWitnessesT7H2.drop 8).take 8 ++ (probeRowWitnessesT7H2.drop 16).take 8 ++ (probeRowWitnessesT7H2.drop 24).take 8).all (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT7H2_part0,probeRowWitnessesT7H2_part1,probeRowWitnessesT7H2_part2,probeRowWitnessesT7H2_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
