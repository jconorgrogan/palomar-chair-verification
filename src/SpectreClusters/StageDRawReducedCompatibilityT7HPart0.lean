module

public import SpectreClusters.StageDRawReducedCompatibilityModel

@[expose] public section

namespace SpectreClusters.StageD.Raw
def reducedPairWitnessesT7H23 : List (Nat × (Nat × Nat)) := [(23,(0,0)),(35,(0,0)),(47,(0,0)),(49,(0,0)),(98,(0,0)),(126,(0,0)),(135,(0,0)),(153,(22,22)),(164,(0,0)),(177,(0,0)),(179,(0,0)),(229,(0,0)),(241,(22,38)),(258,(0,0))]
set_option maxRecDepth 100000 in
theorem reducedPairWitnessesT7H23_checked : reducedCompatibilityCheck .t7h 23 reducedPairWitnessesT7H23 = true := by rfl
def reducedPairWitnessesT7H35 : List (Nat × (Nat × Nat)) := [(23,(0,0)),(35,(0,0)),(47,(0,0)),(49,(0,0)),(98,(0,0)),(126,(0,0)),(135,(0,0)),(153,(0,0)),(164,(22,22)),(177,(0,0)),(179,(0,0)),(229,(0,0)),(241,(0,0)),(258,(0,0))]
set_option maxRecDepth 100000 in
theorem reducedPairWitnessesT7H35_checked : reducedCompatibilityCheck .t7h 35 reducedPairWitnessesT7H35 = true := by rfl
def reducedPairWitnessesT7H47 : List (Nat × (Nat × Nat)) := [(23,(0,0)),(35,(0,0)),(47,(0,0)),(49,(0,0)),(98,(0,0)),(126,(0,0)),(135,(14,27)),(153,(0,0)),(164,(0,0)),(177,(14,14)),(179,(0,0)),(229,(0,0)),(241,(0,0)),(258,(0,0))]
set_option maxRecDepth 100000 in
theorem reducedPairWitnessesT7H47_checked : reducedCompatibilityCheck .t7h 47 reducedPairWitnessesT7H47 = true := by rfl
def reducedPairWitnessesT7H49 : List (Nat × (Nat × Nat)) := [(23,(0,0)),(35,(0,0)),(47,(0,0)),(49,(0,0)),(98,(0,0)),(126,(0,0)),(135,(0,0)),(153,(0,0)),(164,(0,0)),(177,(0,0)),(179,(14,14)),(229,(0,0)),(241,(0,0)),(258,(0,0))]
set_option maxRecDepth 100000 in
theorem reducedPairWitnessesT7H49_checked : reducedCompatibilityCheck .t7h 49 reducedPairWitnessesT7H49 = true := by rfl
end SpectreClusters.StageD.Raw
