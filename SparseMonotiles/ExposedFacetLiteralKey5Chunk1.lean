module

public import SparseMonotiles.ExposedFacetLiteralKeyChunks
public import Mathlib.Tactic.FinCases
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk6
public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk7

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem exposedFacetLiteralKey5Chunk1 : ∀ j : Fin 32,
    ∃ b ∈ IndexedData5.geometry.profile ⟨128+j.val,by omega⟩,
      b.toKeyData 19200 ∈ keys5 := by
  intro j
  fin_cases j
  · refine ⟨IndexedData5.key209,by decide,?_⟩
    rw [indexedKeyDecode5_209]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key210,by decide,?_⟩
    rw [indexedKeyDecode5_210]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key211,by decide,?_⟩
    rw [indexedKeyDecode5_211]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key212,by decide,?_⟩
    rw [indexedKeyDecode5_212]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key213,by decide,?_⟩
    rw [indexedKeyDecode5_213]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key214,by decide,?_⟩
    rw [indexedKeyDecode5_214]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key215,by decide,?_⟩
    rw [indexedKeyDecode5_215]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key216,by decide,?_⟩
    rw [indexedKeyDecode5_216]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key220,by decide,?_⟩
    rw [indexedKeyDecode5_220]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key221,by decide,?_⟩
    rw [indexedKeyDecode5_221]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key222,by decide,?_⟩
    rw [indexedKeyDecode5_222]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key223,by decide,?_⟩
    rw [indexedKeyDecode5_223]
    exact atlasWitness_keys5Chunk6_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key227,by decide,?_⟩
    rw [indexedKeyDecode5_227]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key228,by decide,?_⟩
    rw [indexedKeyDecode5_228]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key229,by decide,?_⟩
    rw [indexedKeyDecode5_229]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key230,by decide,?_⟩
    rw [indexedKeyDecode5_230]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key231,by decide,?_⟩
    rw [indexedKeyDecode5_231]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key235,by decide,?_⟩
    rw [indexedKeyDecode5_235]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key236,by decide,?_⟩
    rw [indexedKeyDecode5_236]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key237,by decide,?_⟩
    rw [indexedKeyDecode5_237]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key238,by decide,?_⟩
    rw [indexedKeyDecode5_238]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key239,by decide,?_⟩
    rw [indexedKeyDecode5_239]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key240,by decide,?_⟩
    rw [indexedKeyDecode5_240]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key241,by decide,?_⟩
    rw [indexedKeyDecode5_241]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key245,by decide,?_⟩
    rw [indexedKeyDecode5_245]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key246,by decide,?_⟩
    rw [indexedKeyDecode5_246]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key247,by decide,?_⟩
    rw [indexedKeyDecode5_247]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key248,by decide,?_⟩
    rw [indexedKeyDecode5_248]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key249,by decide,?_⟩
    rw [indexedKeyDecode5_249]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key250,by decide,?_⟩
    rw [indexedKeyDecode5_250]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key251,by decide,?_⟩
    rw [indexedKeyDecode5_251]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)
  · refine ⟨IndexedData5.key255,by decide,?_⟩
    rw [indexedKeyDecode5_255]
    exact atlasWitness_keys5Chunk7_mem (List.get_mem _ _)

#print axioms exposedFacetLiteralKey5Chunk1
end SparseMonotiles.Canonical
