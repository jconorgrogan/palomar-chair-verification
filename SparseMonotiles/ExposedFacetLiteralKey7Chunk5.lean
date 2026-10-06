module

public import SparseMonotiles.ExposedFacetLiteralKeyChunks
public import Mathlib.Tactic.FinCases
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk22
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk23
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk24
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk25
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk26
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk27

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem exposedFacetLiteralKey7Chunk5 : ∀ j : Fin 128,
    ∃ b ∈ IndexedData7.geometry.profile ⟨640+j.val,by omega⟩,
      b.toKeyData 188160 ∈ keys7 := by
  intro j
  fin_cases j
  · refine ⟨IndexedData7.key732,by decide,?_⟩
    rw [indexedKeyDecode7_732]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key733,by decide,?_⟩
    rw [indexedKeyDecode7_733]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key734,by decide,?_⟩
    rw [indexedKeyDecode7_734]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key735,by decide,?_⟩
    rw [indexedKeyDecode7_735]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key736,by decide,?_⟩
    rw [indexedKeyDecode7_736]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key738,by decide,?_⟩
    rw [indexedKeyDecode7_738]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key739,by decide,?_⟩
    rw [indexedKeyDecode7_739]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key740,by decide,?_⟩
    rw [indexedKeyDecode7_740]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key741,by decide,?_⟩
    rw [indexedKeyDecode7_741]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key742,by decide,?_⟩
    rw [indexedKeyDecode7_742]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key744,by decide,?_⟩
    rw [indexedKeyDecode7_744]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key745,by decide,?_⟩
    rw [indexedKeyDecode7_745]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key746,by decide,?_⟩
    rw [indexedKeyDecode7_746]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key747,by decide,?_⟩
    rw [indexedKeyDecode7_747]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key748,by decide,?_⟩
    rw [indexedKeyDecode7_748]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key749,by decide,?_⟩
    rw [indexedKeyDecode7_749]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key751,by decide,?_⟩
    rw [indexedKeyDecode7_751]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key752,by decide,?_⟩
    rw [indexedKeyDecode7_752]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key753,by decide,?_⟩
    rw [indexedKeyDecode7_753]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key754,by decide,?_⟩
    rw [indexedKeyDecode7_754]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key756,by decide,?_⟩
    rw [indexedKeyDecode7_756]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key757,by decide,?_⟩
    rw [indexedKeyDecode7_757]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key758,by decide,?_⟩
    rw [indexedKeyDecode7_758]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key759,by decide,?_⟩
    rw [indexedKeyDecode7_759]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key760,by decide,?_⟩
    rw [indexedKeyDecode7_760]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key761,by decide,?_⟩
    rw [indexedKeyDecode7_761]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key762,by decide,?_⟩
    rw [indexedKeyDecode7_762]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key763,by decide,?_⟩
    rw [indexedKeyDecode7_763]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key765,by decide,?_⟩
    rw [indexedKeyDecode7_765]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key766,by decide,?_⟩
    rw [indexedKeyDecode7_766]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key767,by decide,?_⟩
    rw [indexedKeyDecode7_767]
    exact atlasWitness_keys7Chunk23_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key768,by decide,?_⟩
    rw [indexedKeyDecode7_768]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key769,by decide,?_⟩
    rw [indexedKeyDecode7_769]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key770,by decide,?_⟩
    rw [indexedKeyDecode7_770]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key771,by decide,?_⟩
    rw [indexedKeyDecode7_771]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key772,by decide,?_⟩
    rw [indexedKeyDecode7_772]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key773,by decide,?_⟩
    rw [indexedKeyDecode7_773]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key774,by decide,?_⟩
    rw [indexedKeyDecode7_774]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key775,by decide,?_⟩
    rw [indexedKeyDecode7_775]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key777,by decide,?_⟩
    rw [indexedKeyDecode7_777]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key778,by decide,?_⟩
    rw [indexedKeyDecode7_778]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key779,by decide,?_⟩
    rw [indexedKeyDecode7_779]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key781,by decide,?_⟩
    rw [indexedKeyDecode7_781]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key782,by decide,?_⟩
    rw [indexedKeyDecode7_782]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key783,by decide,?_⟩
    rw [indexedKeyDecode7_783]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key784,by decide,?_⟩
    rw [indexedKeyDecode7_784]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key785,by decide,?_⟩
    rw [indexedKeyDecode7_785]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key786,by decide,?_⟩
    rw [indexedKeyDecode7_786]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key787,by decide,?_⟩
    rw [indexedKeyDecode7_787]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key788,by decide,?_⟩
    rw [indexedKeyDecode7_788]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key789,by decide,?_⟩
    rw [indexedKeyDecode7_789]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key791,by decide,?_⟩
    rw [indexedKeyDecode7_791]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key792,by decide,?_⟩
    rw [indexedKeyDecode7_792]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key793,by decide,?_⟩
    rw [indexedKeyDecode7_793]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key794,by decide,?_⟩
    rw [indexedKeyDecode7_794]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key795,by decide,?_⟩
    rw [indexedKeyDecode7_795]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key796,by decide,?_⟩
    rw [indexedKeyDecode7_796]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key797,by decide,?_⟩
    rw [indexedKeyDecode7_797]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key798,by decide,?_⟩
    rw [indexedKeyDecode7_798]
    exact atlasWitness_keys7Chunk24_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key800,by decide,?_⟩
    rw [indexedKeyDecode7_800]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key801,by decide,?_⟩
    rw [indexedKeyDecode7_801]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key802,by decide,?_⟩
    rw [indexedKeyDecode7_802]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key803,by decide,?_⟩
    rw [indexedKeyDecode7_803]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key804,by decide,?_⟩
    rw [indexedKeyDecode7_804]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key805,by decide,?_⟩
    rw [indexedKeyDecode7_805]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key806,by decide,?_⟩
    rw [indexedKeyDecode7_806]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key807,by decide,?_⟩
    rw [indexedKeyDecode7_807]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key809,by decide,?_⟩
    rw [indexedKeyDecode7_809]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key810,by decide,?_⟩
    rw [indexedKeyDecode7_810]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key811,by decide,?_⟩
    rw [indexedKeyDecode7_811]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key812,by decide,?_⟩
    rw [indexedKeyDecode7_812]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key814,by decide,?_⟩
    rw [indexedKeyDecode7_814]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key815,by decide,?_⟩
    rw [indexedKeyDecode7_815]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key816,by decide,?_⟩
    rw [indexedKeyDecode7_816]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key817,by decide,?_⟩
    rw [indexedKeyDecode7_817]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key818,by decide,?_⟩
    rw [indexedKeyDecode7_818]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key819,by decide,?_⟩
    rw [indexedKeyDecode7_819]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key820,by decide,?_⟩
    rw [indexedKeyDecode7_820]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key821,by decide,?_⟩
    rw [indexedKeyDecode7_821]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key822,by decide,?_⟩
    rw [indexedKeyDecode7_822]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key823,by decide,?_⟩
    rw [indexedKeyDecode7_823]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key824,by decide,?_⟩
    rw [indexedKeyDecode7_824]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key825,by decide,?_⟩
    rw [indexedKeyDecode7_825]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key827,by decide,?_⟩
    rw [indexedKeyDecode7_827]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key828,by decide,?_⟩
    rw [indexedKeyDecode7_828]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key829,by decide,?_⟩
    rw [indexedKeyDecode7_829]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key830,by decide,?_⟩
    rw [indexedKeyDecode7_830]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key831,by decide,?_⟩
    rw [indexedKeyDecode7_831]
    exact atlasWitness_keys7Chunk25_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key832,by decide,?_⟩
    rw [indexedKeyDecode7_832]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key833,by decide,?_⟩
    rw [indexedKeyDecode7_833]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key835,by decide,?_⟩
    rw [indexedKeyDecode7_835]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key836,by decide,?_⟩
    rw [indexedKeyDecode7_836]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key837,by decide,?_⟩
    rw [indexedKeyDecode7_837]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key838,by decide,?_⟩
    rw [indexedKeyDecode7_838]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key839,by decide,?_⟩
    rw [indexedKeyDecode7_839]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key840,by decide,?_⟩
    rw [indexedKeyDecode7_840]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key841,by decide,?_⟩
    rw [indexedKeyDecode7_841]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key843,by decide,?_⟩
    rw [indexedKeyDecode7_843]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key844,by decide,?_⟩
    rw [indexedKeyDecode7_844]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key845,by decide,?_⟩
    rw [indexedKeyDecode7_845]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key846,by decide,?_⟩
    rw [indexedKeyDecode7_846]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key847,by decide,?_⟩
    rw [indexedKeyDecode7_847]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key848,by decide,?_⟩
    rw [indexedKeyDecode7_848]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key849,by decide,?_⟩
    rw [indexedKeyDecode7_849]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key851,by decide,?_⟩
    rw [indexedKeyDecode7_851]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key852,by decide,?_⟩
    rw [indexedKeyDecode7_852]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key853,by decide,?_⟩
    rw [indexedKeyDecode7_853]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key854,by decide,?_⟩
    rw [indexedKeyDecode7_854]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key855,by decide,?_⟩
    rw [indexedKeyDecode7_855]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key857,by decide,?_⟩
    rw [indexedKeyDecode7_857]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key858,by decide,?_⟩
    rw [indexedKeyDecode7_858]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key859,by decide,?_⟩
    rw [indexedKeyDecode7_859]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key860,by decide,?_⟩
    rw [indexedKeyDecode7_860]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key861,by decide,?_⟩
    rw [indexedKeyDecode7_861]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key862,by decide,?_⟩
    rw [indexedKeyDecode7_862]
    exact atlasWitness_keys7Chunk26_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key864,by decide,?_⟩
    rw [indexedKeyDecode7_864]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key865,by decide,?_⟩
    rw [indexedKeyDecode7_865]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key866,by decide,?_⟩
    rw [indexedKeyDecode7_866]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key867,by decide,?_⟩
    rw [indexedKeyDecode7_867]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key868,by decide,?_⟩
    rw [indexedKeyDecode7_868]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key869,by decide,?_⟩
    rw [indexedKeyDecode7_869]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key871,by decide,?_⟩
    rw [indexedKeyDecode7_871]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key872,by decide,?_⟩
    rw [indexedKeyDecode7_872]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key873,by decide,?_⟩
    rw [indexedKeyDecode7_873]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key874,by decide,?_⟩
    rw [indexedKeyDecode7_874]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key875,by decide,?_⟩
    rw [indexedKeyDecode7_875]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key877,by decide,?_⟩
    rw [indexedKeyDecode7_877]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key878,by decide,?_⟩
    rw [indexedKeyDecode7_878]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)

#print axioms exposedFacetLiteralKey7Chunk5
end SparseMonotiles.Canonical
