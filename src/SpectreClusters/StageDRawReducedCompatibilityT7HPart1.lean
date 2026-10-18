module

public import SpectreClusters.StageDRawReducedCompatibilityModel

@[expose] public section

namespace SpectreClusters.StageD.Raw
def reducedPairWitnessesT7H98 : List (Nat × (Nat × Nat)) := [(23,(0,0)),(35,(0,0)),(47,(0,0)),(49,(0,0)),(98,(0,0)),(126,(0,0)),(135,(0,0)),(153,(0,0)),(164,(0,0)),(177,(0,0)),(179,(0,0)),(229,(54,54)),(241,(0,0)),(258,(0,0))]
set_option maxRecDepth 100000 in
theorem reducedPairWitnessesT7H98_checked : reducedCompatibilityCheck .t7h 98 reducedPairWitnessesT7H98 = true := by rfl
def reducedPairWitnessesT7H126 : List (Nat × (Nat × Nat)) := [(23,(0,0)),(35,(0,0)),(47,(0,0)),(49,(0,0)),(98,(0,0)),(126,(0,0)),(135,(0,0)),(153,(0,0)),(164,(0,0)),(177,(0,0)),(179,(0,0)),(229,(0,0)),(241,(0,0)),(258,(38,38))]
set_option maxRecDepth 100000 in
theorem reducedPairWitnessesT7H126_checked : reducedCompatibilityCheck .t7h 126 reducedPairWitnessesT7H126 = true := by rfl
def reducedPairWitnessesT7H135 : List (Nat × (Nat × Nat)) := [(23,(0,0)),(35,(0,0)),(47,(27,14)),(49,(0,0)),(98,(0,0)),(126,(0,0)),(135,(0,0)),(153,(0,0)),(164,(0,0)),(177,(29,72)),(179,(0,0)),(229,(0,0)),(241,(0,0)),(258,(0,0))]
set_option maxRecDepth 100000 in
theorem reducedPairWitnessesT7H135_checked : reducedCompatibilityCheck .t7h 135 reducedPairWitnessesT7H135 = true := by rfl
def reducedPairWitnessesT7H153 : List (Nat × (Nat × Nat)) := [(23,(22,22)),(35,(0,0)),(47,(0,0)),(49,(0,0)),(98,(0,0)),(126,(0,0)),(135,(0,0)),(153,(0,0)),(164,(0,0)),(177,(0,0)),(179,(0,0)),(229,(0,0)),(241,(22,38)),(258,(0,0))]
set_option maxRecDepth 100000 in
theorem reducedPairWitnessesT7H153_checked : reducedCompatibilityCheck .t7h 153 reducedPairWitnessesT7H153 = true := by rfl
end SpectreClusters.StageD.Raw
