module

public import SparseMonotiles.ExposedFacetLiteralKeyChunks
public import Mathlib.Tactic.FinCases
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk27
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk28
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk29
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk30
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk31

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem exposedFacetLiteralKey7Chunk6 : ∀ j : Fin 128,
    ∃ b ∈ IndexedData7.geometry.profile ⟨768+j.val,by omega⟩,
      b.toKeyData 188160 ∈ keys7 := by
  intro j
  fin_cases j
  · refine ⟨IndexedData7.key879,by decide,?_⟩
    rw [indexedKeyDecode7_879]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key880,by decide,?_⟩
    rw [indexedKeyDecode7_880]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key881,by decide,?_⟩
    rw [indexedKeyDecode7_881]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key882,by decide,?_⟩
    rw [indexedKeyDecode7_882]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key883,by decide,?_⟩
    rw [indexedKeyDecode7_883]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key884,by decide,?_⟩
    rw [indexedKeyDecode7_884]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key885,by decide,?_⟩
    rw [indexedKeyDecode7_885]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key886,by decide,?_⟩
    rw [indexedKeyDecode7_886]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key887,by decide,?_⟩
    rw [indexedKeyDecode7_887]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key889,by decide,?_⟩
    rw [indexedKeyDecode7_889]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key890,by decide,?_⟩
    rw [indexedKeyDecode7_890]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key891,by decide,?_⟩
    rw [indexedKeyDecode7_891]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key892,by decide,?_⟩
    rw [indexedKeyDecode7_892]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key893,by decide,?_⟩
    rw [indexedKeyDecode7_893]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key895,by decide,?_⟩
    rw [indexedKeyDecode7_895]
    exact atlasWitness_keys7Chunk27_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key896,by decide,?_⟩
    rw [indexedKeyDecode7_896]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key897,by decide,?_⟩
    rw [indexedKeyDecode7_897]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key898,by decide,?_⟩
    rw [indexedKeyDecode7_898]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key899,by decide,?_⟩
    rw [indexedKeyDecode7_899]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key900,by decide,?_⟩
    rw [indexedKeyDecode7_900]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key901,by decide,?_⟩
    rw [indexedKeyDecode7_901]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key903,by decide,?_⟩
    rw [indexedKeyDecode7_903]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key904,by decide,?_⟩
    rw [indexedKeyDecode7_904]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key905,by decide,?_⟩
    rw [indexedKeyDecode7_905]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key906,by decide,?_⟩
    rw [indexedKeyDecode7_906]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key907,by decide,?_⟩
    rw [indexedKeyDecode7_907]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key908,by decide,?_⟩
    rw [indexedKeyDecode7_908]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key909,by decide,?_⟩
    rw [indexedKeyDecode7_909]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key910,by decide,?_⟩
    rw [indexedKeyDecode7_910]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key911,by decide,?_⟩
    rw [indexedKeyDecode7_911]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key912,by decide,?_⟩
    rw [indexedKeyDecode7_912]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key914,by decide,?_⟩
    rw [indexedKeyDecode7_914]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key915,by decide,?_⟩
    rw [indexedKeyDecode7_915]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key916,by decide,?_⟩
    rw [indexedKeyDecode7_916]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key917,by decide,?_⟩
    rw [indexedKeyDecode7_917]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key918,by decide,?_⟩
    rw [indexedKeyDecode7_918]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key920,by decide,?_⟩
    rw [indexedKeyDecode7_920]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key921,by decide,?_⟩
    rw [indexedKeyDecode7_921]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key922,by decide,?_⟩
    rw [indexedKeyDecode7_922]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key923,by decide,?_⟩
    rw [indexedKeyDecode7_923]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key924,by decide,?_⟩
    rw [indexedKeyDecode7_924]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key926,by decide,?_⟩
    rw [indexedKeyDecode7_926]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key927,by decide,?_⟩
    rw [indexedKeyDecode7_927]
    exact atlasWitness_keys7Chunk28_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key928,by decide,?_⟩
    rw [indexedKeyDecode7_928]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key929,by decide,?_⟩
    rw [indexedKeyDecode7_929]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key930,by decide,?_⟩
    rw [indexedKeyDecode7_930]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key931,by decide,?_⟩
    rw [indexedKeyDecode7_931]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key932,by decide,?_⟩
    rw [indexedKeyDecode7_932]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key934,by decide,?_⟩
    rw [indexedKeyDecode7_934]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key935,by decide,?_⟩
    rw [indexedKeyDecode7_935]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key936,by decide,?_⟩
    rw [indexedKeyDecode7_936]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key937,by decide,?_⟩
    rw [indexedKeyDecode7_937]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key938,by decide,?_⟩
    rw [indexedKeyDecode7_938]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key939,by decide,?_⟩
    rw [indexedKeyDecode7_939]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key940,by decide,?_⟩
    rw [indexedKeyDecode7_940]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key941,by decide,?_⟩
    rw [indexedKeyDecode7_941]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key942,by decide,?_⟩
    rw [indexedKeyDecode7_942]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key943,by decide,?_⟩
    rw [indexedKeyDecode7_943]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key944,by decide,?_⟩
    rw [indexedKeyDecode7_944]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key946,by decide,?_⟩
    rw [indexedKeyDecode7_946]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key947,by decide,?_⟩
    rw [indexedKeyDecode7_947]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key948,by decide,?_⟩
    rw [indexedKeyDecode7_948]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key949,by decide,?_⟩
    rw [indexedKeyDecode7_949]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key951,by decide,?_⟩
    rw [indexedKeyDecode7_951]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key952,by decide,?_⟩
    rw [indexedKeyDecode7_952]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key953,by decide,?_⟩
    rw [indexedKeyDecode7_953]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key954,by decide,?_⟩
    rw [indexedKeyDecode7_954]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key955,by decide,?_⟩
    rw [indexedKeyDecode7_955]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key956,by decide,?_⟩
    rw [indexedKeyDecode7_956]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key957,by decide,?_⟩
    rw [indexedKeyDecode7_957]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key958,by decide,?_⟩
    rw [indexedKeyDecode7_958]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key959,by decide,?_⟩
    rw [indexedKeyDecode7_959]
    exact atlasWitness_keys7Chunk29_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key961,by decide,?_⟩
    rw [indexedKeyDecode7_961]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key962,by decide,?_⟩
    rw [indexedKeyDecode7_962]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key963,by decide,?_⟩
    rw [indexedKeyDecode7_963]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key964,by decide,?_⟩
    rw [indexedKeyDecode7_964]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key965,by decide,?_⟩
    rw [indexedKeyDecode7_965]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key966,by decide,?_⟩
    rw [indexedKeyDecode7_966]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key967,by decide,?_⟩
    rw [indexedKeyDecode7_967]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key968,by decide,?_⟩
    rw [indexedKeyDecode7_968]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key969,by decide,?_⟩
    rw [indexedKeyDecode7_969]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key970,by decide,?_⟩
    rw [indexedKeyDecode7_970]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key972,by decide,?_⟩
    rw [indexedKeyDecode7_972]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key973,by decide,?_⟩
    rw [indexedKeyDecode7_973]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key974,by decide,?_⟩
    rw [indexedKeyDecode7_974]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key976,by decide,?_⟩
    rw [indexedKeyDecode7_976]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key977,by decide,?_⟩
    rw [indexedKeyDecode7_977]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key978,by decide,?_⟩
    rw [indexedKeyDecode7_978]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key979,by decide,?_⟩
    rw [indexedKeyDecode7_979]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key980,by decide,?_⟩
    rw [indexedKeyDecode7_980]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key981,by decide,?_⟩
    rw [indexedKeyDecode7_981]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key982,by decide,?_⟩
    rw [indexedKeyDecode7_982]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key983,by decide,?_⟩
    rw [indexedKeyDecode7_983]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key984,by decide,?_⟩
    rw [indexedKeyDecode7_984]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key985,by decide,?_⟩
    rw [indexedKeyDecode7_985]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key986,by decide,?_⟩
    rw [indexedKeyDecode7_986]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key988,by decide,?_⟩
    rw [indexedKeyDecode7_988]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key989,by decide,?_⟩
    rw [indexedKeyDecode7_989]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key990,by decide,?_⟩
    rw [indexedKeyDecode7_990]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key991,by decide,?_⟩
    rw [indexedKeyDecode7_991]
    exact atlasWitness_keys7Chunk30_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key992,by decide,?_⟩
    rw [indexedKeyDecode7_992]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key993,by decide,?_⟩
    rw [indexedKeyDecode7_993]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key995,by decide,?_⟩
    rw [indexedKeyDecode7_995]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key996,by decide,?_⟩
    rw [indexedKeyDecode7_996]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key997,by decide,?_⟩
    rw [indexedKeyDecode7_997]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key998,by decide,?_⟩
    rw [indexedKeyDecode7_998]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key999,by decide,?_⟩
    rw [indexedKeyDecode7_999]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1000,by decide,?_⟩
    rw [indexedKeyDecode7_1000]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1002,by decide,?_⟩
    rw [indexedKeyDecode7_1002]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1003,by decide,?_⟩
    rw [indexedKeyDecode7_1003]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1004,by decide,?_⟩
    rw [indexedKeyDecode7_1004]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1005,by decide,?_⟩
    rw [indexedKeyDecode7_1005]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1006,by decide,?_⟩
    rw [indexedKeyDecode7_1006]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1007,by decide,?_⟩
    rw [indexedKeyDecode7_1007]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1008,by decide,?_⟩
    rw [indexedKeyDecode7_1008]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1009,by decide,?_⟩
    rw [indexedKeyDecode7_1009]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1010,by decide,?_⟩
    rw [indexedKeyDecode7_1010]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1011,by decide,?_⟩
    rw [indexedKeyDecode7_1011]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1013,by decide,?_⟩
    rw [indexedKeyDecode7_1013]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1014,by decide,?_⟩
    rw [indexedKeyDecode7_1014]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1015,by decide,?_⟩
    rw [indexedKeyDecode7_1015]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1016,by decide,?_⟩
    rw [indexedKeyDecode7_1016]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1017,by decide,?_⟩
    rw [indexedKeyDecode7_1017]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1018,by decide,?_⟩
    rw [indexedKeyDecode7_1018]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1019,by decide,?_⟩
    rw [indexedKeyDecode7_1019]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1020,by decide,?_⟩
    rw [indexedKeyDecode7_1020]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1021,by decide,?_⟩
    rw [indexedKeyDecode7_1021]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key1023,by decide,?_⟩
    rw [indexedKeyDecode7_1023]
    exact atlasWitness_keys7Chunk31_mem (List.get_mem _ _)

#print axioms exposedFacetLiteralKey7Chunk6
end SparseMonotiles.Canonical
