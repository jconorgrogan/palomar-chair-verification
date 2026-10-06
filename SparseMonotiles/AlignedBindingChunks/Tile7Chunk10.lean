module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk10

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk10_aligned : ∀ k ∈ keys7Chunk10,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk10, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨280, by decide⟩, IndexedData7.key320, by decide, canonicalPose7_320, canonicalMatch7_320, indexedKeyDecode7_320⟩
  · exact ⟨⟨281, by decide⟩, IndexedData7.key321, by decide, canonicalPose7_321, canonicalMatch7_321, indexedKeyDecode7_321⟩
  · exact ⟨⟨282, by decide⟩, IndexedData7.key322, by decide, canonicalPose7_322, canonicalMatch7_322, indexedKeyDecode7_322⟩
  · exact ⟨⟨282, by decide⟩, IndexedData7.key323, by decide, canonicalPose7_323, canonicalMatch7_323, indexedKeyDecode7_323⟩
  · exact ⟨⟨283, by decide⟩, IndexedData7.key324, by decide, canonicalPose7_324, canonicalMatch7_324, indexedKeyDecode7_324⟩
  · exact ⟨⟨284, by decide⟩, IndexedData7.key325, by decide, canonicalPose7_325, canonicalMatch7_325, indexedKeyDecode7_325⟩
  · exact ⟨⟨285, by decide⟩, IndexedData7.key326, by decide, canonicalPose7_326, canonicalMatch7_326, indexedKeyDecode7_326⟩
  · exact ⟨⟨286, by decide⟩, IndexedData7.key327, by decide, canonicalPose7_327, canonicalMatch7_327, indexedKeyDecode7_327⟩
  · exact ⟨⟨287, by decide⟩, IndexedData7.key328, by decide, canonicalPose7_328, canonicalMatch7_328, indexedKeyDecode7_328⟩
  · exact ⟨⟨288, by decide⟩, IndexedData7.key329, by decide, canonicalPose7_329, canonicalMatch7_329, indexedKeyDecode7_329⟩
  · exact ⟨⟨288, by decide⟩, IndexedData7.key330, by decide, canonicalPose7_330, canonicalMatch7_330, indexedKeyDecode7_330⟩
  · exact ⟨⟨289, by decide⟩, IndexedData7.key331, by decide, canonicalPose7_331, canonicalMatch7_331, indexedKeyDecode7_331⟩
  · exact ⟨⟨290, by decide⟩, IndexedData7.key332, by decide, canonicalPose7_332, canonicalMatch7_332, indexedKeyDecode7_332⟩
  · exact ⟨⟨291, by decide⟩, IndexedData7.key333, by decide, canonicalPose7_333, canonicalMatch7_333, indexedKeyDecode7_333⟩
  · exact ⟨⟨292, by decide⟩, IndexedData7.key334, by decide, canonicalPose7_334, canonicalMatch7_334, indexedKeyDecode7_334⟩
  · exact ⟨⟨293, by decide⟩, IndexedData7.key335, by decide, canonicalPose7_335, canonicalMatch7_335, indexedKeyDecode7_335⟩
  · exact ⟨⟨294, by decide⟩, IndexedData7.key336, by decide, canonicalPose7_336, canonicalMatch7_336, indexedKeyDecode7_336⟩
  · exact ⟨⟨295, by decide⟩, IndexedData7.key337, by decide, canonicalPose7_337, canonicalMatch7_337, indexedKeyDecode7_337⟩
  · exact ⟨⟨296, by decide⟩, IndexedData7.key338, by decide, canonicalPose7_338, canonicalMatch7_338, indexedKeyDecode7_338⟩
  · exact ⟨⟨297, by decide⟩, IndexedData7.key339, by decide, canonicalPose7_339, canonicalMatch7_339, indexedKeyDecode7_339⟩
  · exact ⟨⟨297, by decide⟩, IndexedData7.key340, by decide, canonicalPose7_340, canonicalMatch7_340, indexedKeyDecode7_340⟩
  · exact ⟨⟨298, by decide⟩, IndexedData7.key341, by decide, canonicalPose7_341, canonicalMatch7_341, indexedKeyDecode7_341⟩
  · exact ⟨⟨299, by decide⟩, IndexedData7.key342, by decide, canonicalPose7_342, canonicalMatch7_342, indexedKeyDecode7_342⟩
  · exact ⟨⟨300, by decide⟩, IndexedData7.key343, by decide, canonicalPose7_343, canonicalMatch7_343, indexedKeyDecode7_343⟩
  · exact ⟨⟨301, by decide⟩, IndexedData7.key344, by decide, canonicalPose7_344, canonicalMatch7_344, indexedKeyDecode7_344⟩
  · exact ⟨⟨302, by decide⟩, IndexedData7.key345, by decide, canonicalPose7_345, canonicalMatch7_345, indexedKeyDecode7_345⟩
  · exact ⟨⟨303, by decide⟩, IndexedData7.key346, by decide, canonicalPose7_346, canonicalMatch7_346, indexedKeyDecode7_346⟩
  · exact ⟨⟨303, by decide⟩, IndexedData7.key347, by decide, canonicalPose7_347, canonicalMatch7_347, indexedKeyDecode7_347⟩
  · exact ⟨⟨304, by decide⟩, IndexedData7.key348, by decide, canonicalPose7_348, canonicalMatch7_348, indexedKeyDecode7_348⟩
  · exact ⟨⟨305, by decide⟩, IndexedData7.key349, by decide, canonicalPose7_349, canonicalMatch7_349, indexedKeyDecode7_349⟩
  · exact ⟨⟨306, by decide⟩, IndexedData7.key350, by decide, canonicalPose7_350, canonicalMatch7_350, indexedKeyDecode7_350⟩
  · exact ⟨⟨307, by decide⟩, IndexedData7.key351, by decide, canonicalPose7_351, canonicalMatch7_351, indexedKeyDecode7_351⟩

#print axioms keys7Chunk10_aligned

end SparseMonotiles.Canonical
