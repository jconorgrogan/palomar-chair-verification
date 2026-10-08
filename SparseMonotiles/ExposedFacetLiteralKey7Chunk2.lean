module

public import SparseMonotiles.ExposedFacetLiteralKeyChunks
public import Mathlib.Tactic.FinCases
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk9
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk10
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk11
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk12
public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk13

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem exposedFacetLiteralKey7Chunk2 : ∀ j : Fin 128,
    ∃ b ∈ IndexedData7.geometry.profile ⟨256+j.val,by omega⟩,
      b.toKeyData 188160 ∈ keys7 := by
  intro j
  fin_cases j
  · refine ⟨IndexedData7.key292,by decide,?_⟩
    rw [indexedKeyDecode7_292]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key293,by decide,?_⟩
    rw [indexedKeyDecode7_293]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key294,by decide,?_⟩
    rw [indexedKeyDecode7_294]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key296,by decide,?_⟩
    rw [indexedKeyDecode7_296]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key297,by decide,?_⟩
    rw [indexedKeyDecode7_297]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key298,by decide,?_⟩
    rw [indexedKeyDecode7_298]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key299,by decide,?_⟩
    rw [indexedKeyDecode7_299]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key300,by decide,?_⟩
    rw [indexedKeyDecode7_300]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key301,by decide,?_⟩
    rw [indexedKeyDecode7_301]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key302,by decide,?_⟩
    rw [indexedKeyDecode7_302]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key304,by decide,?_⟩
    rw [indexedKeyDecode7_304]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key305,by decide,?_⟩
    rw [indexedKeyDecode7_305]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key307,by decide,?_⟩
    rw [indexedKeyDecode7_307]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key308,by decide,?_⟩
    rw [indexedKeyDecode7_308]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key309,by decide,?_⟩
    rw [indexedKeyDecode7_309]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key310,by decide,?_⟩
    rw [indexedKeyDecode7_310]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key311,by decide,?_⟩
    rw [indexedKeyDecode7_311]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key312,by decide,?_⟩
    rw [indexedKeyDecode7_312]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key313,by decide,?_⟩
    rw [indexedKeyDecode7_313]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key314,by decide,?_⟩
    rw [indexedKeyDecode7_314]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key315,by decide,?_⟩
    rw [indexedKeyDecode7_315]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key316,by decide,?_⟩
    rw [indexedKeyDecode7_316]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key318,by decide,?_⟩
    rw [indexedKeyDecode7_318]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key319,by decide,?_⟩
    rw [indexedKeyDecode7_319]
    exact atlasWitness_keys7Chunk9_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key320,by decide,?_⟩
    rw [indexedKeyDecode7_320]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key321,by decide,?_⟩
    rw [indexedKeyDecode7_321]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key322,by decide,?_⟩
    rw [indexedKeyDecode7_322]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key324,by decide,?_⟩
    rw [indexedKeyDecode7_324]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key325,by decide,?_⟩
    rw [indexedKeyDecode7_325]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key326,by decide,?_⟩
    rw [indexedKeyDecode7_326]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key327,by decide,?_⟩
    rw [indexedKeyDecode7_327]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key328,by decide,?_⟩
    rw [indexedKeyDecode7_328]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key329,by decide,?_⟩
    rw [indexedKeyDecode7_329]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key331,by decide,?_⟩
    rw [indexedKeyDecode7_331]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key332,by decide,?_⟩
    rw [indexedKeyDecode7_332]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key333,by decide,?_⟩
    rw [indexedKeyDecode7_333]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key334,by decide,?_⟩
    rw [indexedKeyDecode7_334]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key335,by decide,?_⟩
    rw [indexedKeyDecode7_335]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key336,by decide,?_⟩
    rw [indexedKeyDecode7_336]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key337,by decide,?_⟩
    rw [indexedKeyDecode7_337]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key338,by decide,?_⟩
    rw [indexedKeyDecode7_338]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key339,by decide,?_⟩
    rw [indexedKeyDecode7_339]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key341,by decide,?_⟩
    rw [indexedKeyDecode7_341]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key342,by decide,?_⟩
    rw [indexedKeyDecode7_342]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key343,by decide,?_⟩
    rw [indexedKeyDecode7_343]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key344,by decide,?_⟩
    rw [indexedKeyDecode7_344]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key345,by decide,?_⟩
    rw [indexedKeyDecode7_345]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key346,by decide,?_⟩
    rw [indexedKeyDecode7_346]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key348,by decide,?_⟩
    rw [indexedKeyDecode7_348]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key349,by decide,?_⟩
    rw [indexedKeyDecode7_349]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key350,by decide,?_⟩
    rw [indexedKeyDecode7_350]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key351,by decide,?_⟩
    rw [indexedKeyDecode7_351]
    exact atlasWitness_keys7Chunk10_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key352,by decide,?_⟩
    rw [indexedKeyDecode7_352]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key353,by decide,?_⟩
    rw [indexedKeyDecode7_353]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key354,by decide,?_⟩
    rw [indexedKeyDecode7_354]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key355,by decide,?_⟩
    rw [indexedKeyDecode7_355]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key356,by decide,?_⟩
    rw [indexedKeyDecode7_356]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key357,by decide,?_⟩
    rw [indexedKeyDecode7_357]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key359,by decide,?_⟩
    rw [indexedKeyDecode7_359]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key360,by decide,?_⟩
    rw [indexedKeyDecode7_360]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key362,by decide,?_⟩
    rw [indexedKeyDecode7_362]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key363,by decide,?_⟩
    rw [indexedKeyDecode7_363]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key364,by decide,?_⟩
    rw [indexedKeyDecode7_364]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key365,by decide,?_⟩
    rw [indexedKeyDecode7_365]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key366,by decide,?_⟩
    rw [indexedKeyDecode7_366]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key367,by decide,?_⟩
    rw [indexedKeyDecode7_367]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key368,by decide,?_⟩
    rw [indexedKeyDecode7_368]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key369,by decide,?_⟩
    rw [indexedKeyDecode7_369]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key370,by decide,?_⟩
    rw [indexedKeyDecode7_370]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key371,by decide,?_⟩
    rw [indexedKeyDecode7_371]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key372,by decide,?_⟩
    rw [indexedKeyDecode7_372]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key373,by decide,?_⟩
    rw [indexedKeyDecode7_373]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key375,by decide,?_⟩
    rw [indexedKeyDecode7_375]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key376,by decide,?_⟩
    rw [indexedKeyDecode7_376]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key377,by decide,?_⟩
    rw [indexedKeyDecode7_377]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key379,by decide,?_⟩
    rw [indexedKeyDecode7_379]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key380,by decide,?_⟩
    rw [indexedKeyDecode7_380]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key381,by decide,?_⟩
    rw [indexedKeyDecode7_381]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key382,by decide,?_⟩
    rw [indexedKeyDecode7_382]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key383,by decide,?_⟩
    rw [indexedKeyDecode7_383]
    exact atlasWitness_keys7Chunk11_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key384,by decide,?_⟩
    rw [indexedKeyDecode7_384]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key385,by decide,?_⟩
    rw [indexedKeyDecode7_385]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key386,by decide,?_⟩
    rw [indexedKeyDecode7_386]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key387,by decide,?_⟩
    rw [indexedKeyDecode7_387]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key388,by decide,?_⟩
    rw [indexedKeyDecode7_388]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key389,by decide,?_⟩
    rw [indexedKeyDecode7_389]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key391,by decide,?_⟩
    rw [indexedKeyDecode7_391]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key392,by decide,?_⟩
    rw [indexedKeyDecode7_392]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key393,by decide,?_⟩
    rw [indexedKeyDecode7_393]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key394,by decide,?_⟩
    rw [indexedKeyDecode7_394]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key395,by decide,?_⟩
    rw [indexedKeyDecode7_395]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key397,by decide,?_⟩
    rw [indexedKeyDecode7_397]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key398,by decide,?_⟩
    rw [indexedKeyDecode7_398]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key399,by decide,?_⟩
    rw [indexedKeyDecode7_399]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key400,by decide,?_⟩
    rw [indexedKeyDecode7_400]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key401,by decide,?_⟩
    rw [indexedKeyDecode7_401]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key402,by decide,?_⟩
    rw [indexedKeyDecode7_402]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key403,by decide,?_⟩
    rw [indexedKeyDecode7_403]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key404,by decide,?_⟩
    rw [indexedKeyDecode7_404]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key405,by decide,?_⟩
    rw [indexedKeyDecode7_405]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key407,by decide,?_⟩
    rw [indexedKeyDecode7_407]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key408,by decide,?_⟩
    rw [indexedKeyDecode7_408]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key410,by decide,?_⟩
    rw [indexedKeyDecode7_410]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key411,by decide,?_⟩
    rw [indexedKeyDecode7_411]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key412,by decide,?_⟩
    rw [indexedKeyDecode7_412]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key413,by decide,?_⟩
    rw [indexedKeyDecode7_413]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key414,by decide,?_⟩
    rw [indexedKeyDecode7_414]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key415,by decide,?_⟩
    rw [indexedKeyDecode7_415]
    exact atlasWitness_keys7Chunk12_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key416,by decide,?_⟩
    rw [indexedKeyDecode7_416]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key418,by decide,?_⟩
    rw [indexedKeyDecode7_418]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key419,by decide,?_⟩
    rw [indexedKeyDecode7_419]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key420,by decide,?_⟩
    rw [indexedKeyDecode7_420]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key421,by decide,?_⟩
    rw [indexedKeyDecode7_421]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key422,by decide,?_⟩
    rw [indexedKeyDecode7_422]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key423,by decide,?_⟩
    rw [indexedKeyDecode7_423]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key424,by decide,?_⟩
    rw [indexedKeyDecode7_424]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key425,by decide,?_⟩
    rw [indexedKeyDecode7_425]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key426,by decide,?_⟩
    rw [indexedKeyDecode7_426]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key427,by decide,?_⟩
    rw [indexedKeyDecode7_427]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key428,by decide,?_⟩
    rw [indexedKeyDecode7_428]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key429,by decide,?_⟩
    rw [indexedKeyDecode7_429]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key431,by decide,?_⟩
    rw [indexedKeyDecode7_431]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key432,by decide,?_⟩
    rw [indexedKeyDecode7_432]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key433,by decide,?_⟩
    rw [indexedKeyDecode7_433]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key434,by decide,?_⟩
    rw [indexedKeyDecode7_434]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key435,by decide,?_⟩
    rw [indexedKeyDecode7_435]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key437,by decide,?_⟩
    rw [indexedKeyDecode7_437]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)
  · refine ⟨IndexedData7.key438,by decide,?_⟩
    rw [indexedKeyDecode7_438]
    exact atlasWitness_keys7Chunk13_mem (List.get_mem _ _)

#print axioms exposedFacetLiteralKey7Chunk2
end SparseMonotiles.Canonical
