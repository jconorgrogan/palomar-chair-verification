module

public import SparseMonotiles.ExposedFacetLiteralKeyChunks
public import Mathlib.Tactic.FinCases
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk13
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk14
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk15
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk16
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk17
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk18

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem exposedFacetLiteralKey7Chunk3 : ∀ j : Fin 128,
    ∃ b ∈ IndexedData7.geometry.profile ⟨384+j.val,by omega⟩,
      b.toKeyData 188160 ∈ keys7 := by
  intro j
  fin_cases j
  · refine ⟨IndexedData7.key439,by decide,?_⟩
    rw [indexedKeyDecode7_439]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key440,by decide,?_⟩
    rw [indexedKeyDecode7_440]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key441,by decide,?_⟩
    rw [indexedKeyDecode7_441]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key442,by decide,?_⟩
    rw [indexedKeyDecode7_442]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key443,by decide,?_⟩
    rw [indexedKeyDecode7_443]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key444,by decide,?_⟩
    rw [indexedKeyDecode7_444]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key445,by decide,?_⟩
    rw [indexedKeyDecode7_445]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key447,by decide,?_⟩
    rw [indexedKeyDecode7_447]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key448,by decide,?_⟩
    rw [indexedKeyDecode7_448]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key449,by decide,?_⟩
    rw [indexedKeyDecode7_449]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key450,by decide,?_⟩
    rw [indexedKeyDecode7_450]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key452,by decide,?_⟩
    rw [indexedKeyDecode7_452]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key453,by decide,?_⟩
    rw [indexedKeyDecode7_453]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key454,by decide,?_⟩
    rw [indexedKeyDecode7_454]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key455,by decide,?_⟩
    rw [indexedKeyDecode7_455]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key456,by decide,?_⟩
    rw [indexedKeyDecode7_456]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key457,by decide,?_⟩
    rw [indexedKeyDecode7_457]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key458,by decide,?_⟩
    rw [indexedKeyDecode7_458]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key459,by decide,?_⟩
    rw [indexedKeyDecode7_459]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key461,by decide,?_⟩
    rw [indexedKeyDecode7_461]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key462,by decide,?_⟩
    rw [indexedKeyDecode7_462]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key463,by decide,?_⟩
    rw [indexedKeyDecode7_463]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key464,by decide,?_⟩
    rw [indexedKeyDecode7_464]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key465,by decide,?_⟩
    rw [indexedKeyDecode7_465]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key467,by decide,?_⟩
    rw [indexedKeyDecode7_467]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key468,by decide,?_⟩
    rw [indexedKeyDecode7_468]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key469,by decide,?_⟩
    rw [indexedKeyDecode7_469]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key470,by decide,?_⟩
    rw [indexedKeyDecode7_470]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key471,by decide,?_⟩
    rw [indexedKeyDecode7_471]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key472,by decide,?_⟩
    rw [indexedKeyDecode7_472]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key473,by decide,?_⟩
    rw [indexedKeyDecode7_473]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key474,by decide,?_⟩
    rw [indexedKeyDecode7_474]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key476,by decide,?_⟩
    rw [indexedKeyDecode7_476]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key477,by decide,?_⟩
    rw [indexedKeyDecode7_477]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key478,by decide,?_⟩
    rw [indexedKeyDecode7_478]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key479,by decide,?_⟩
    rw [indexedKeyDecode7_479]
    exact atlasWitness_keys7Chunk14_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key480,by decide,?_⟩
    rw [indexedKeyDecode7_480]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key481,by decide,?_⟩
    rw [indexedKeyDecode7_481]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key482,by decide,?_⟩
    rw [indexedKeyDecode7_482]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key483,by decide,?_⟩
    rw [indexedKeyDecode7_483]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key484,by decide,?_⟩
    rw [indexedKeyDecode7_484]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key485,by decide,?_⟩
    rw [indexedKeyDecode7_485]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key486,by decide,?_⟩
    rw [indexedKeyDecode7_486]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key488,by decide,?_⟩
    rw [indexedKeyDecode7_488]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key489,by decide,?_⟩
    rw [indexedKeyDecode7_489]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key490,by decide,?_⟩
    rw [indexedKeyDecode7_490]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key491,by decide,?_⟩
    rw [indexedKeyDecode7_491]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key492,by decide,?_⟩
    rw [indexedKeyDecode7_492]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key493,by decide,?_⟩
    rw [indexedKeyDecode7_493]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key494,by decide,?_⟩
    rw [indexedKeyDecode7_494]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key496,by decide,?_⟩
    rw [indexedKeyDecode7_496]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key497,by decide,?_⟩
    rw [indexedKeyDecode7_497]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key498,by decide,?_⟩
    rw [indexedKeyDecode7_498]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key499,by decide,?_⟩
    rw [indexedKeyDecode7_499]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key501,by decide,?_⟩
    rw [indexedKeyDecode7_501]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key502,by decide,?_⟩
    rw [indexedKeyDecode7_502]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key503,by decide,?_⟩
    rw [indexedKeyDecode7_503]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key504,by decide,?_⟩
    rw [indexedKeyDecode7_504]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key506,by decide,?_⟩
    rw [indexedKeyDecode7_506]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key508,by decide,?_⟩
    rw [indexedKeyDecode7_508]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key509,by decide,?_⟩
    rw [indexedKeyDecode7_509]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key510,by decide,?_⟩
    rw [indexedKeyDecode7_510]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key511,by decide,?_⟩
    rw [indexedKeyDecode7_511]
    exact atlasWitness_keys7Chunk15_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key512,by decide,?_⟩
    rw [indexedKeyDecode7_512]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key513,by decide,?_⟩
    rw [indexedKeyDecode7_513]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key514,by decide,?_⟩
    rw [indexedKeyDecode7_514]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key516,by decide,?_⟩
    rw [indexedKeyDecode7_516]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key517,by decide,?_⟩
    rw [indexedKeyDecode7_517]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key518,by decide,?_⟩
    rw [indexedKeyDecode7_518]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key519,by decide,?_⟩
    rw [indexedKeyDecode7_519]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key520,by decide,?_⟩
    rw [indexedKeyDecode7_520]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key521,by decide,?_⟩
    rw [indexedKeyDecode7_521]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key522,by decide,?_⟩
    rw [indexedKeyDecode7_522]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key523,by decide,?_⟩
    rw [indexedKeyDecode7_523]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key524,by decide,?_⟩
    rw [indexedKeyDecode7_524]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key525,by decide,?_⟩
    rw [indexedKeyDecode7_525]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key527,by decide,?_⟩
    rw [indexedKeyDecode7_527]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key528,by decide,?_⟩
    rw [indexedKeyDecode7_528]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key529,by decide,?_⟩
    rw [indexedKeyDecode7_529]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key530,by decide,?_⟩
    rw [indexedKeyDecode7_530]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key531,by decide,?_⟩
    rw [indexedKeyDecode7_531]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key532,by decide,?_⟩
    rw [indexedKeyDecode7_532]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key533,by decide,?_⟩
    rw [indexedKeyDecode7_533]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key534,by decide,?_⟩
    rw [indexedKeyDecode7_534]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key535,by decide,?_⟩
    rw [indexedKeyDecode7_535]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key536,by decide,?_⟩
    rw [indexedKeyDecode7_536]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key538,by decide,?_⟩
    rw [indexedKeyDecode7_538]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key539,by decide,?_⟩
    rw [indexedKeyDecode7_539]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key540,by decide,?_⟩
    rw [indexedKeyDecode7_540]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key541,by decide,?_⟩
    rw [indexedKeyDecode7_541]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key542,by decide,?_⟩
    rw [indexedKeyDecode7_542]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key543,by decide,?_⟩
    rw [indexedKeyDecode7_543]
    exact atlasWitness_keys7Chunk16_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key544,by decide,?_⟩
    rw [indexedKeyDecode7_544]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key546,by decide,?_⟩
    rw [indexedKeyDecode7_546]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key547,by decide,?_⟩
    rw [indexedKeyDecode7_547]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key548,by decide,?_⟩
    rw [indexedKeyDecode7_548]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key550,by decide,?_⟩
    rw [indexedKeyDecode7_550]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key551,by decide,?_⟩
    rw [indexedKeyDecode7_551]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key552,by decide,?_⟩
    rw [indexedKeyDecode7_552]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key553,by decide,?_⟩
    rw [indexedKeyDecode7_553]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key554,by decide,?_⟩
    rw [indexedKeyDecode7_554]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key555,by decide,?_⟩
    rw [indexedKeyDecode7_555]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key557,by decide,?_⟩
    rw [indexedKeyDecode7_557]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key558,by decide,?_⟩
    rw [indexedKeyDecode7_558]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key559,by decide,?_⟩
    rw [indexedKeyDecode7_559]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key560,by decide,?_⟩
    rw [indexedKeyDecode7_560]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key561,by decide,?_⟩
    rw [indexedKeyDecode7_561]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key562,by decide,?_⟩
    rw [indexedKeyDecode7_562]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key563,by decide,?_⟩
    rw [indexedKeyDecode7_563]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key564,by decide,?_⟩
    rw [indexedKeyDecode7_564]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key565,by decide,?_⟩
    rw [indexedKeyDecode7_565]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key567,by decide,?_⟩
    rw [indexedKeyDecode7_567]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key568,by decide,?_⟩
    rw [indexedKeyDecode7_568]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key569,by decide,?_⟩
    rw [indexedKeyDecode7_569]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key570,by decide,?_⟩
    rw [indexedKeyDecode7_570]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key571,by decide,?_⟩
    rw [indexedKeyDecode7_571]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key572,by decide,?_⟩
    rw [indexedKeyDecode7_572]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key574,by decide,?_⟩
    rw [indexedKeyDecode7_574]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key575,by decide,?_⟩
    rw [indexedKeyDecode7_575]
    exact atlasWitness_keys7Chunk17_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key576,by decide,?_⟩
    rw [indexedKeyDecode7_576]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key577,by decide,?_⟩
    rw [indexedKeyDecode7_577]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key578,by decide,?_⟩
    rw [indexedKeyDecode7_578]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key579,by decide,?_⟩
    rw [indexedKeyDecode7_579]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key580,by decide,?_⟩
    rw [indexedKeyDecode7_580]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key581,by decide,?_⟩
    rw [indexedKeyDecode7_581]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key582,by decide,?_⟩
    rw [indexedKeyDecode7_582]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key583,by decide,?_⟩
    rw [indexedKeyDecode7_583]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key585,by decide,?_⟩
    rw [indexedKeyDecode7_585]
    exact atlasWitness_keys7Chunk18_mem (List.get_mem _ _)

#print axioms exposedFacetLiteralKey7Chunk3
end SparseMonotiles.Canonical
