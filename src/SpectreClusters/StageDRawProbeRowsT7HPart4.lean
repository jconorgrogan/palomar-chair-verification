module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT7H4 : List (List Nat × Nat) := [([241,47,98,258,179,164],128),([23,135,98,258,179,164],129),([153,135,98,258,179,164],130),([241,135,98,258,179,164],131),([23,177,98,258,179,164],132),([153,177,98,258,179,164],133),([241,177,98,258,179,164],134),([23,47,229,258,179,164],135),([153,47,229,258,179,164],136),([241,47,229,258,179,164],137),([23,135,229,258,179,164],138),([153,135,229,258,179,164],139),([241,135,229,258,179,164],140),([23,177,229,258,179,164],141),([153,177,229,258,179,164],142),([241,177,229,258,179,164],143)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H4_part0 : ((probeRowWitnessesT7H4.drop 0).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H4_part1 : ((probeRowWitnessesT7H4.drop 8).take 8).all
    (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by rfl
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT7H4_checked : probeRowWitnessesT7H4.all (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true := by
  change ((probeRowWitnessesT7H4.drop 0).take 8 ++ (probeRowWitnessesT7H4.drop 8).take 8).all (fun wi => wordCoversRowB .t7h wi.1 wi.2) = true
  simp only [List.all_append,probeRowWitnessesT7H4_part0,probeRowWitnessesT7H4_part1,Bool.and_self]
end SpectreClusters.StageD.Raw
