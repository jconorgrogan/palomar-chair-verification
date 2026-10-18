module

public import SpectreClusters.StageDRawReducedCompatibilityT7HPart0
public import SpectreClusters.StageDRawReducedCompatibilityT7HPart1
public import SpectreClusters.StageDRawReducedCompatibilityT7HPart2
public import SpectreClusters.StageDRawReducedCompatibilityT7HPart3

@[expose] public section

namespace SpectreClusters.StageD.Raw
def reducedDomainT7H : List Nat := [23,35,47,49,98,126,135,153,164,177,179,229,241,258]
theorem reducedCompatibilityT7H_sound (a b : Nat) (ha : a ∈ reducedDomainT7H) (hb : b ∈ reducedDomainT7H)
    (hc : (candidateList .t7h).getD a fallback = (candidateList .t7h).getD b fallback ∨
      DisjointCells (clusterPlacementCells ((candidateList .t7h).getD a fallback))
        (clusterPlacementCells ((candidateList .t7h).getD b fallback))) : idCompatible .t7h a b = true := by
  simp only [reducedDomainT7H,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reducedCompatibilityCheck_sound .t7h 23 b reducedPairWitnessesT7H23
      reducedPairWitnessesT7H23_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H23,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 35 b reducedPairWitnessesT7H35
      reducedPairWitnessesT7H35_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H35,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 47 b reducedPairWitnessesT7H47
      reducedPairWitnessesT7H47_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H47,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 49 b reducedPairWitnessesT7H49
      reducedPairWitnessesT7H49_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H49,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 98 b reducedPairWitnessesT7H98
      reducedPairWitnessesT7H98_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H98,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 126 b reducedPairWitnessesT7H126
      reducedPairWitnessesT7H126_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H126,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 135 b reducedPairWitnessesT7H135
      reducedPairWitnessesT7H135_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H135,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 153 b reducedPairWitnessesT7H153
      reducedPairWitnessesT7H153_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H153,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 164 b reducedPairWitnessesT7H164
      reducedPairWitnessesT7H164_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H164,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 177 b reducedPairWitnessesT7H177
      reducedPairWitnessesT7H177_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H177,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 179 b reducedPairWitnessesT7H179
      reducedPairWitnessesT7H179_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H179,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 229 b reducedPairWitnessesT7H229
      reducedPairWitnessesT7H229_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H229,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 241 b reducedPairWitnessesT7H241
      reducedPairWitnessesT7H241_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H241,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t7h 258 b reducedPairWitnessesT7H258
      reducedPairWitnessesT7H258_checked (by simpa only [reducedDomainT7H,reducedPairWitnessesT7H258,List.map_cons,List.map_nil] using hb) hc
end SpectreClusters.StageD.Raw
