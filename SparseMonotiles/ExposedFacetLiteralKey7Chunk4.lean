module

public import SparseMonotiles.ExposedFacetLiteralKeyChunks
public import Mathlib.Tactic.FinCases
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk18
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk19
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk20
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk21
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk22

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem exposedFacetLiteralKey7Chunk4 : ∀ j : Fin 128,
    ∃ b ∈ IndexedData7.geometry.profile ⟨512+j.val,by omega⟩,
      b.toKeyData 188160 ∈ keys7 := by
  intro j
  fin_cases j
  · refine ⟨IndexedData7.key586,by decide,?_⟩
    rw [indexedKeyDecode7_586]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key587,by decide,?_⟩
    rw [indexedKeyDecode7_587]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key588,by decide,?_⟩
    rw [indexedKeyDecode7_588]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key589,by decide,?_⟩
    rw [indexedKeyDecode7_589]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key591,by decide,?_⟩
    rw [indexedKeyDecode7_591]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key592,by decide,?_⟩
    rw [indexedKeyDecode7_592]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key593,by decide,?_⟩
    rw [indexedKeyDecode7_593]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key594,by decide,?_⟩
    rw [indexedKeyDecode7_594]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key595,by decide,?_⟩
    rw [indexedKeyDecode7_595]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key596,by decide,?_⟩
    rw [indexedKeyDecode7_596]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key597,by decide,?_⟩
    rw [indexedKeyDecode7_597]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key598,by decide,?_⟩
    rw [indexedKeyDecode7_598]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key599,by decide,?_⟩
    rw [indexedKeyDecode7_599]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key601,by decide,?_⟩
    rw [indexedKeyDecode7_601]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key602,by decide,?_⟩
    rw [indexedKeyDecode7_602]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key604,by decide,?_⟩
    rw [indexedKeyDecode7_604]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key605,by decide,?_⟩
    rw [indexedKeyDecode7_605]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key606,by decide,?_⟩
    rw [indexedKeyDecode7_606]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key607,by decide,?_⟩
    rw [indexedKeyDecode7_607]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key608,by decide,?_⟩
    rw [indexedKeyDecode7_608]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key609,by decide,?_⟩
    rw [indexedKeyDecode7_609]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key610,by decide,?_⟩
    rw [indexedKeyDecode7_610]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key612,by decide,?_⟩
    rw [indexedKeyDecode7_612]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key613,by decide,?_⟩
    rw [indexedKeyDecode7_613]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key614,by decide,?_⟩
    rw [indexedKeyDecode7_614]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key615,by decide,?_⟩
    rw [indexedKeyDecode7_615]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key616,by decide,?_⟩
    rw [indexedKeyDecode7_616]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key617,by decide,?_⟩
    rw [indexedKeyDecode7_617]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key618,by decide,?_⟩
    rw [indexedKeyDecode7_618]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key619,by decide,?_⟩
    rw [indexedKeyDecode7_619]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key620,by decide,?_⟩
    rw [indexedKeyDecode7_620]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key621,by decide,?_⟩
    rw [indexedKeyDecode7_621]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key622,by decide,?_⟩
    rw [indexedKeyDecode7_622]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key623,by decide,?_⟩
    rw [indexedKeyDecode7_623]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key625,by decide,?_⟩
    rw [indexedKeyDecode7_625]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key626,by decide,?_⟩
    rw [indexedKeyDecode7_626]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key627,by decide,?_⟩
    rw [indexedKeyDecode7_627]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key628,by decide,?_⟩
    rw [indexedKeyDecode7_628]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key629,by decide,?_⟩
    rw [indexedKeyDecode7_629]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key631,by decide,?_⟩
    rw [indexedKeyDecode7_631]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key632,by decide,?_⟩
    rw [indexedKeyDecode7_632]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key633,by decide,?_⟩
    rw [indexedKeyDecode7_633]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key634,by decide,?_⟩
    rw [indexedKeyDecode7_634]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key635,by decide,?_⟩
    rw [indexedKeyDecode7_635]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key636,by decide,?_⟩
    rw [indexedKeyDecode7_636]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key637,by decide,?_⟩
    rw [indexedKeyDecode7_637]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key638,by decide,?_⟩
    rw [indexedKeyDecode7_638]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key639,by decide,?_⟩
    rw [indexedKeyDecode7_639]
    exact atlasWitness_keys7Chunk19_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key641,by decide,?_⟩
    rw [indexedKeyDecode7_641]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key642,by decide,?_⟩
    rw [indexedKeyDecode7_642]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key643,by decide,?_⟩
    rw [indexedKeyDecode7_643]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key645,by decide,?_⟩
    rw [indexedKeyDecode7_645]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key646,by decide,?_⟩
    rw [indexedKeyDecode7_646]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key647,by decide,?_⟩
    rw [indexedKeyDecode7_647]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key648,by decide,?_⟩
    rw [indexedKeyDecode7_648]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key649,by decide,?_⟩
    rw [indexedKeyDecode7_649]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key650,by decide,?_⟩
    rw [indexedKeyDecode7_650]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key651,by decide,?_⟩
    rw [indexedKeyDecode7_651]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key652,by decide,?_⟩
    rw [indexedKeyDecode7_652]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key653,by decide,?_⟩
    rw [indexedKeyDecode7_653]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key654,by decide,?_⟩
    rw [indexedKeyDecode7_654]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key655,by decide,?_⟩
    rw [indexedKeyDecode7_655]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key657,by decide,?_⟩
    rw [indexedKeyDecode7_657]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key658,by decide,?_⟩
    rw [indexedKeyDecode7_658]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key660,by decide,?_⟩
    rw [indexedKeyDecode7_660]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key661,by decide,?_⟩
    rw [indexedKeyDecode7_661]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key662,by decide,?_⟩
    rw [indexedKeyDecode7_662]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key663,by decide,?_⟩
    rw [indexedKeyDecode7_663]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key664,by decide,?_⟩
    rw [indexedKeyDecode7_664]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key665,by decide,?_⟩
    rw [indexedKeyDecode7_665]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key666,by decide,?_⟩
    rw [indexedKeyDecode7_666]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key667,by decide,?_⟩
    rw [indexedKeyDecode7_667]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key668,by decide,?_⟩
    rw [indexedKeyDecode7_668]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key669,by decide,?_⟩
    rw [indexedKeyDecode7_669]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key670,by decide,?_⟩
    rw [indexedKeyDecode7_670]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key671,by decide,?_⟩
    rw [indexedKeyDecode7_671]
    exact atlasWitness_keys7Chunk20_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key673,by decide,?_⟩
    rw [indexedKeyDecode7_673]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key674,by decide,?_⟩
    rw [indexedKeyDecode7_674]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key675,by decide,?_⟩
    rw [indexedKeyDecode7_675]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key676,by decide,?_⟩
    rw [indexedKeyDecode7_676]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key678,by decide,?_⟩
    rw [indexedKeyDecode7_678]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key679,by decide,?_⟩
    rw [indexedKeyDecode7_679]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key680,by decide,?_⟩
    rw [indexedKeyDecode7_680]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key681,by decide,?_⟩
    rw [indexedKeyDecode7_681]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key682,by decide,?_⟩
    rw [indexedKeyDecode7_682]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key683,by decide,?_⟩
    rw [indexedKeyDecode7_683]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key684,by decide,?_⟩
    rw [indexedKeyDecode7_684]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key685,by decide,?_⟩
    rw [indexedKeyDecode7_685]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key687,by decide,?_⟩
    rw [indexedKeyDecode7_687]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key688,by decide,?_⟩
    rw [indexedKeyDecode7_688]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key689,by decide,?_⟩
    rw [indexedKeyDecode7_689]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key690,by decide,?_⟩
    rw [indexedKeyDecode7_690]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key691,by decide,?_⟩
    rw [indexedKeyDecode7_691]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key693,by decide,?_⟩
    rw [indexedKeyDecode7_693]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key694,by decide,?_⟩
    rw [indexedKeyDecode7_694]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key695,by decide,?_⟩
    rw [indexedKeyDecode7_695]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key696,by decide,?_⟩
    rw [indexedKeyDecode7_696]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key697,by decide,?_⟩
    rw [indexedKeyDecode7_697]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key698,by decide,?_⟩
    rw [indexedKeyDecode7_698]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key699,by decide,?_⟩
    rw [indexedKeyDecode7_699]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key700,by decide,?_⟩
    rw [indexedKeyDecode7_700]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key702,by decide,?_⟩
    rw [indexedKeyDecode7_702]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key703,by decide,?_⟩
    rw [indexedKeyDecode7_703]
    exact atlasWitness_keys7Chunk21_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key704,by decide,?_⟩
    rw [indexedKeyDecode7_704]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key705,by decide,?_⟩
    rw [indexedKeyDecode7_705]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key706,by decide,?_⟩
    rw [indexedKeyDecode7_706]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key707,by decide,?_⟩
    rw [indexedKeyDecode7_707]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key708,by decide,?_⟩
    rw [indexedKeyDecode7_708]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key709,by decide,?_⟩
    rw [indexedKeyDecode7_709]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key710,by decide,?_⟩
    rw [indexedKeyDecode7_710]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key712,by decide,?_⟩
    rw [indexedKeyDecode7_712]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key713,by decide,?_⟩
    rw [indexedKeyDecode7_713]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key714,by decide,?_⟩
    rw [indexedKeyDecode7_714]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key715,by decide,?_⟩
    rw [indexedKeyDecode7_715]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key717,by decide,?_⟩
    rw [indexedKeyDecode7_717]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key718,by decide,?_⟩
    rw [indexedKeyDecode7_718]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key719,by decide,?_⟩
    rw [indexedKeyDecode7_719]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key720,by decide,?_⟩
    rw [indexedKeyDecode7_720]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key721,by decide,?_⟩
    rw [indexedKeyDecode7_721]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key722,by decide,?_⟩
    rw [indexedKeyDecode7_722]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key723,by decide,?_⟩
    rw [indexedKeyDecode7_723]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key724,by decide,?_⟩
    rw [indexedKeyDecode7_724]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key725,by decide,?_⟩
    rw [indexedKeyDecode7_725]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key726,by decide,?_⟩
    rw [indexedKeyDecode7_726]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key727,by decide,?_⟩
    rw [indexedKeyDecode7_727]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key728,by decide,?_⟩
    rw [indexedKeyDecode7_728]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key730,by decide,?_⟩
    rw [indexedKeyDecode7_730]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key731,by decide,?_⟩
    rw [indexedKeyDecode7_731]
    exact atlasWitness_keys7Chunk22_mem (List.get_mem _ _)

#print axioms exposedFacetLiteralKey7Chunk4
end SparseMonotiles.Canonical
