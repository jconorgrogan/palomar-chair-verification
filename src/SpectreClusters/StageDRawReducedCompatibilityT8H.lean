module

public import SpectreClusters.StageDRawReducedCompatibilityT8HPart0
public import SpectreClusters.StageDRawReducedCompatibilityT8HPart1
public import SpectreClusters.StageDRawReducedCompatibilityT8HPart2
public import SpectreClusters.StageDRawReducedCompatibilityT8HPart3
public import SpectreClusters.StageDRawReducedCompatibilityT8HPart4
public import SpectreClusters.StageDRawReducedCompatibilityT8HPart5
public import SpectreClusters.StageDRawReducedCompatibilityT8HPart6
public import SpectreClusters.StageDRawReducedCompatibilityT8HPart7
public import SpectreClusters.StageDRawReducedCompatibilityT8HPart8
public import SpectreClusters.StageDRawReducedCompatibilityT8HPart9
public import SpectreClusters.StageDRawReducedCompatibilityT8HPart10

@[expose] public section

namespace SpectreClusters.StageD.Raw
def reducedDomainT8H : List Nat := [16,23,28,30,37,40,45,48,55,85,90,95,100,104,107,114,116,118,123,137,144,148,155,162,168,172,177,180,187,191,194,206,217,228,232,236,239,244,249,251,256]
theorem reducedCompatibilityT8H_sound (a b : Nat) (ha : a ∈ reducedDomainT8H) (hb : b ∈ reducedDomainT8H)
    (hc : (candidateList .t8h).getD a fallback = (candidateList .t8h).getD b fallback ∨
      DisjointCells (clusterPlacementCells ((candidateList .t8h).getD a fallback))
        (clusterPlacementCells ((candidateList .t8h).getD b fallback))) : idCompatible .t8h a b = true := by
  simp only [reducedDomainT8H,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reducedCompatibilityCheck_sound .t8h 16 b reducedPairWitnessesT8H16
      reducedPairWitnessesT8H16_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H16,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 23 b reducedPairWitnessesT8H23
      reducedPairWitnessesT8H23_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H23,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 28 b reducedPairWitnessesT8H28
      reducedPairWitnessesT8H28_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H28,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 30 b reducedPairWitnessesT8H30
      reducedPairWitnessesT8H30_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H30,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 37 b reducedPairWitnessesT8H37
      reducedPairWitnessesT8H37_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H37,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 40 b reducedPairWitnessesT8H40
      reducedPairWitnessesT8H40_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H40,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 45 b reducedPairWitnessesT8H45
      reducedPairWitnessesT8H45_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H45,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 48 b reducedPairWitnessesT8H48
      reducedPairWitnessesT8H48_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H48,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 55 b reducedPairWitnessesT8H55
      reducedPairWitnessesT8H55_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H55,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 85 b reducedPairWitnessesT8H85
      reducedPairWitnessesT8H85_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H85,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 90 b reducedPairWitnessesT8H90
      reducedPairWitnessesT8H90_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H90,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 95 b reducedPairWitnessesT8H95
      reducedPairWitnessesT8H95_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H95,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 100 b reducedPairWitnessesT8H100
      reducedPairWitnessesT8H100_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H100,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 104 b reducedPairWitnessesT8H104
      reducedPairWitnessesT8H104_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H104,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 107 b reducedPairWitnessesT8H107
      reducedPairWitnessesT8H107_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H107,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 114 b reducedPairWitnessesT8H114
      reducedPairWitnessesT8H114_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H114,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 116 b reducedPairWitnessesT8H116
      reducedPairWitnessesT8H116_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H116,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 118 b reducedPairWitnessesT8H118
      reducedPairWitnessesT8H118_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H118,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 123 b reducedPairWitnessesT8H123
      reducedPairWitnessesT8H123_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H123,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 137 b reducedPairWitnessesT8H137
      reducedPairWitnessesT8H137_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H137,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 144 b reducedPairWitnessesT8H144
      reducedPairWitnessesT8H144_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H144,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 148 b reducedPairWitnessesT8H148
      reducedPairWitnessesT8H148_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H148,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 155 b reducedPairWitnessesT8H155
      reducedPairWitnessesT8H155_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H155,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 162 b reducedPairWitnessesT8H162
      reducedPairWitnessesT8H162_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H162,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 168 b reducedPairWitnessesT8H168
      reducedPairWitnessesT8H168_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H168,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 172 b reducedPairWitnessesT8H172
      reducedPairWitnessesT8H172_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H172,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 177 b reducedPairWitnessesT8H177
      reducedPairWitnessesT8H177_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H177,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 180 b reducedPairWitnessesT8H180
      reducedPairWitnessesT8H180_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H180,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 187 b reducedPairWitnessesT8H187
      reducedPairWitnessesT8H187_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H187,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 191 b reducedPairWitnessesT8H191
      reducedPairWitnessesT8H191_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H191,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 194 b reducedPairWitnessesT8H194
      reducedPairWitnessesT8H194_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H194,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 206 b reducedPairWitnessesT8H206
      reducedPairWitnessesT8H206_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H206,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 217 b reducedPairWitnessesT8H217
      reducedPairWitnessesT8H217_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H217,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 228 b reducedPairWitnessesT8H228
      reducedPairWitnessesT8H228_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H228,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 232 b reducedPairWitnessesT8H232
      reducedPairWitnessesT8H232_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H232,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 236 b reducedPairWitnessesT8H236
      reducedPairWitnessesT8H236_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H236,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 239 b reducedPairWitnessesT8H239
      reducedPairWitnessesT8H239_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H239,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 244 b reducedPairWitnessesT8H244
      reducedPairWitnessesT8H244_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H244,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 249 b reducedPairWitnessesT8H249
      reducedPairWitnessesT8H249_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H249,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 251 b reducedPairWitnessesT8H251
      reducedPairWitnessesT8H251_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H251,List.map_cons,List.map_nil] using hb) hc
  · exact reducedCompatibilityCheck_sound .t8h 256 b reducedPairWitnessesT8H256
      reducedPairWitnessesT8H256_checked (by simpa only [reducedDomainT8H,reducedPairWitnessesT8H256,List.map_cons,List.map_nil] using hb) hc
end SpectreClusters.StageD.Raw
