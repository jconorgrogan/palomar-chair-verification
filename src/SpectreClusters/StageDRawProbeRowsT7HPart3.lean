module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT7H3 : List (List Nat × Nat) := [([23,177,98,258,49,164],96),([153,177,98,258,49,164],97),([241,177,98,258,49,164],98),([23,47,229,258,49,164],99),([153,47,229,258,49,164],100),([241,47,229,258,49,164],101),([23,135,229,258,49,164],102),([153,135,229,258,49,164],103),([241,135,229,258,49,164],104),([23,177,229,258,49,164],105),([153,177,229,258,49,164],106),([241,177,229,258,49,164],107),([23,47,98,126,179,164],108),([153,47,98,126,179,164],109),([241,47,98,126,179,164],110),([23,135,98,126,179,164],111),([153,135,98,126,179,164],112),([241,135,98,126,179,164],113),([23,177,98,126,179,164],114),([153,177,98,126,179,164],115),([241,177,98,126,179,164],116),([23,47,229,126,179,164],117),([153,47,229,126,179,164],118),([241,47,229,126,179,164],119),([23,135,229,126,179,164],120),([153,135,229,126,179,164],121),([241,135,229,126,179,164],122),([23,177,229,126,179,164],123),([153,177,229,126,179,164],124),([241,177,229,126,179,164],125),([23,47,98,258,179,164],126),([153,47,98,258,179,164],127)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H3_part0 : ((probeRowWitnessesT7H3.drop 0).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H3_part1 : ((probeRowWitnessesT7H3.drop 8).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H3_part2 : ((probeRowWitnessesT7H3.drop 16).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H3_part3 : ((probeRowWitnessesT7H3.drop 24).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H3_checked : probeRowWitnessesT7H3.all (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT7H3.drop 0).take 8 ++ (probeRowWitnessesT7H3.drop 8).take 8 ++ (probeRowWitnessesT7H3.drop 16).take 8 ++ (probeRowWitnessesT7H3.drop 24).take 8).all (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT7H3_part0,probeRowWitnessesT7H3_part1,probeRowWitnessesT7H3_part2,probeRowWitnessesT7H3_part3,Bool.and_self]
end SpectreClusters.StageD.Raw
