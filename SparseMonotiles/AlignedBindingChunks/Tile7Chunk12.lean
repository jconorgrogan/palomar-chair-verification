module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk12

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk12_aligned : ∀ k ∈ keys7Chunk12,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk12, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨336, by decide⟩, IndexedData7.key384, by decide, canonicalPose7_384, canonicalMatch7_384, indexedKeyDecode7_384⟩
  · exact ⟨⟨337, by decide⟩, IndexedData7.key385, by decide, canonicalPose7_385, canonicalMatch7_385, indexedKeyDecode7_385⟩
  · exact ⟨⟨338, by decide⟩, IndexedData7.key386, by decide, canonicalPose7_386, canonicalMatch7_386, indexedKeyDecode7_386⟩
  · exact ⟨⟨339, by decide⟩, IndexedData7.key387, by decide, canonicalPose7_387, canonicalMatch7_387, indexedKeyDecode7_387⟩
  · exact ⟨⟨340, by decide⟩, IndexedData7.key388, by decide, canonicalPose7_388, canonicalMatch7_388, indexedKeyDecode7_388⟩
  · exact ⟨⟨341, by decide⟩, IndexedData7.key389, by decide, canonicalPose7_389, canonicalMatch7_389, indexedKeyDecode7_389⟩
  · exact ⟨⟨341, by decide⟩, IndexedData7.key390, by decide, canonicalPose7_390, canonicalMatch7_390, indexedKeyDecode7_390⟩
  · exact ⟨⟨342, by decide⟩, IndexedData7.key391, by decide, canonicalPose7_391, canonicalMatch7_391, indexedKeyDecode7_391⟩
  · exact ⟨⟨343, by decide⟩, IndexedData7.key392, by decide, canonicalPose7_392, canonicalMatch7_392, indexedKeyDecode7_392⟩
  · exact ⟨⟨344, by decide⟩, IndexedData7.key393, by decide, canonicalPose7_393, canonicalMatch7_393, indexedKeyDecode7_393⟩
  · exact ⟨⟨345, by decide⟩, IndexedData7.key394, by decide, canonicalPose7_394, canonicalMatch7_394, indexedKeyDecode7_394⟩
  · exact ⟨⟨346, by decide⟩, IndexedData7.key395, by decide, canonicalPose7_395, canonicalMatch7_395, indexedKeyDecode7_395⟩
  · exact ⟨⟨346, by decide⟩, IndexedData7.key396, by decide, canonicalPose7_396, canonicalMatch7_396, indexedKeyDecode7_396⟩
  · exact ⟨⟨347, by decide⟩, IndexedData7.key397, by decide, canonicalPose7_397, canonicalMatch7_397, indexedKeyDecode7_397⟩
  · exact ⟨⟨348, by decide⟩, IndexedData7.key398, by decide, canonicalPose7_398, canonicalMatch7_398, indexedKeyDecode7_398⟩
  · exact ⟨⟨349, by decide⟩, IndexedData7.key399, by decide, canonicalPose7_399, canonicalMatch7_399, indexedKeyDecode7_399⟩
  · exact ⟨⟨350, by decide⟩, IndexedData7.key400, by decide, canonicalPose7_400, canonicalMatch7_400, indexedKeyDecode7_400⟩
  · exact ⟨⟨351, by decide⟩, IndexedData7.key401, by decide, canonicalPose7_401, canonicalMatch7_401, indexedKeyDecode7_401⟩
  · exact ⟨⟨352, by decide⟩, IndexedData7.key402, by decide, canonicalPose7_402, canonicalMatch7_402, indexedKeyDecode7_402⟩
  · exact ⟨⟨353, by decide⟩, IndexedData7.key403, by decide, canonicalPose7_403, canonicalMatch7_403, indexedKeyDecode7_403⟩
  · exact ⟨⟨354, by decide⟩, IndexedData7.key404, by decide, canonicalPose7_404, canonicalMatch7_404, indexedKeyDecode7_404⟩
  · exact ⟨⟨355, by decide⟩, IndexedData7.key405, by decide, canonicalPose7_405, canonicalMatch7_405, indexedKeyDecode7_405⟩
  · exact ⟨⟨355, by decide⟩, IndexedData7.key406, by decide, canonicalPose7_406, canonicalMatch7_406, indexedKeyDecode7_406⟩
  · exact ⟨⟨356, by decide⟩, IndexedData7.key407, by decide, canonicalPose7_407, canonicalMatch7_407, indexedKeyDecode7_407⟩
  · exact ⟨⟨357, by decide⟩, IndexedData7.key408, by decide, canonicalPose7_408, canonicalMatch7_408, indexedKeyDecode7_408⟩
  · exact ⟨⟨357, by decide⟩, IndexedData7.key409, by decide, canonicalPose7_409, canonicalMatch7_409, indexedKeyDecode7_409⟩
  · exact ⟨⟨358, by decide⟩, IndexedData7.key410, by decide, canonicalPose7_410, canonicalMatch7_410, indexedKeyDecode7_410⟩
  · exact ⟨⟨359, by decide⟩, IndexedData7.key411, by decide, canonicalPose7_411, canonicalMatch7_411, indexedKeyDecode7_411⟩
  · exact ⟨⟨360, by decide⟩, IndexedData7.key412, by decide, canonicalPose7_412, canonicalMatch7_412, indexedKeyDecode7_412⟩
  · exact ⟨⟨361, by decide⟩, IndexedData7.key413, by decide, canonicalPose7_413, canonicalMatch7_413, indexedKeyDecode7_413⟩
  · exact ⟨⟨362, by decide⟩, IndexedData7.key414, by decide, canonicalPose7_414, canonicalMatch7_414, indexedKeyDecode7_414⟩
  · exact ⟨⟨363, by decide⟩, IndexedData7.key415, by decide, canonicalPose7_415, canonicalMatch7_415, indexedKeyDecode7_415⟩

#print axioms keys7Chunk12_aligned

end SparseMonotiles.Canonical
