module

public import SpectreClusters.StageDRawReducedCompatibilityModel

@[expose] public section

namespace SpectreClusters.StageD.Raw
def reducedPairWitnessesT7H241 : List (Nat × (Nat × Nat)) := [(23,(38,22)),(35,(0,0)),(47,(0,0)),(49,(0,0)),(98,(0,0)),(126,(0,0)),(135,(0,0)),(153,(38,22)),(164,(0,0)),(177,(0,0)),(179,(0,0)),(229,(0,0)),(241,(0,0)),(258,(0,0))]
set_option maxRecDepth 100000 in
theorem reducedPairWitnessesT7H241_checked : reducedCompatibilityCheck .t7h 241 reducedPairWitnessesT7H241 = true := by rfl
def reducedPairWitnessesT7H258 : List (Nat × (Nat × Nat)) := [(23,(0,0)),(35,(0,0)),(47,(0,0)),(49,(0,0)),(98,(0,0)),(126,(38,38)),(135,(0,0)),(153,(0,0)),(164,(0,0)),(177,(0,0)),(179,(0,0)),(229,(0,0)),(241,(0,0)),(258,(0,0))]
set_option maxRecDepth 100000 in
theorem reducedPairWitnessesT7H258_checked : reducedCompatibilityCheck .t7h 258 reducedPairWitnessesT7H258 = true := by rfl
end SpectreClusters.StageD.Raw
