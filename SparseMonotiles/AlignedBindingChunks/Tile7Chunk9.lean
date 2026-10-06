module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk9

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk9_aligned : ∀ k ∈ keys7Chunk9,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk9, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨252, by decide⟩, IndexedData7.key288, by decide, canonicalPose7_288, canonicalMatch7_288, indexedKeyDecode7_288⟩
  · exact ⟨⟨253, by decide⟩, IndexedData7.key289, by decide, canonicalPose7_289, canonicalMatch7_289, indexedKeyDecode7_289⟩
  · exact ⟨⟨254, by decide⟩, IndexedData7.key290, by decide, canonicalPose7_290, canonicalMatch7_290, indexedKeyDecode7_290⟩
  · exact ⟨⟨255, by decide⟩, IndexedData7.key291, by decide, canonicalPose7_291, canonicalMatch7_291, indexedKeyDecode7_291⟩
  · exact ⟨⟨256, by decide⟩, IndexedData7.key292, by decide, canonicalPose7_292, canonicalMatch7_292, indexedKeyDecode7_292⟩
  · exact ⟨⟨257, by decide⟩, IndexedData7.key293, by decide, canonicalPose7_293, canonicalMatch7_293, indexedKeyDecode7_293⟩
  · exact ⟨⟨258, by decide⟩, IndexedData7.key294, by decide, canonicalPose7_294, canonicalMatch7_294, indexedKeyDecode7_294⟩
  · exact ⟨⟨258, by decide⟩, IndexedData7.key295, by decide, canonicalPose7_295, canonicalMatch7_295, indexedKeyDecode7_295⟩
  · exact ⟨⟨259, by decide⟩, IndexedData7.key296, by decide, canonicalPose7_296, canonicalMatch7_296, indexedKeyDecode7_296⟩
  · exact ⟨⟨260, by decide⟩, IndexedData7.key297, by decide, canonicalPose7_297, canonicalMatch7_297, indexedKeyDecode7_297⟩
  · exact ⟨⟨261, by decide⟩, IndexedData7.key298, by decide, canonicalPose7_298, canonicalMatch7_298, indexedKeyDecode7_298⟩
  · exact ⟨⟨262, by decide⟩, IndexedData7.key299, by decide, canonicalPose7_299, canonicalMatch7_299, indexedKeyDecode7_299⟩
  · exact ⟨⟨263, by decide⟩, IndexedData7.key300, by decide, canonicalPose7_300, canonicalMatch7_300, indexedKeyDecode7_300⟩
  · exact ⟨⟨264, by decide⟩, IndexedData7.key301, by decide, canonicalPose7_301, canonicalMatch7_301, indexedKeyDecode7_301⟩
  · exact ⟨⟨265, by decide⟩, IndexedData7.key302, by decide, canonicalPose7_302, canonicalMatch7_302, indexedKeyDecode7_302⟩
  · exact ⟨⟨265, by decide⟩, IndexedData7.key303, by decide, canonicalPose7_303, canonicalMatch7_303, indexedKeyDecode7_303⟩
  · exact ⟨⟨266, by decide⟩, IndexedData7.key304, by decide, canonicalPose7_304, canonicalMatch7_304, indexedKeyDecode7_304⟩
  · exact ⟨⟨267, by decide⟩, IndexedData7.key305, by decide, canonicalPose7_305, canonicalMatch7_305, indexedKeyDecode7_305⟩
  · exact ⟨⟨267, by decide⟩, IndexedData7.key306, by decide, canonicalPose7_306, canonicalMatch7_306, indexedKeyDecode7_306⟩
  · exact ⟨⟨268, by decide⟩, IndexedData7.key307, by decide, canonicalPose7_307, canonicalMatch7_307, indexedKeyDecode7_307⟩
  · exact ⟨⟨269, by decide⟩, IndexedData7.key308, by decide, canonicalPose7_308, canonicalMatch7_308, indexedKeyDecode7_308⟩
  · exact ⟨⟨270, by decide⟩, IndexedData7.key309, by decide, canonicalPose7_309, canonicalMatch7_309, indexedKeyDecode7_309⟩
  · exact ⟨⟨271, by decide⟩, IndexedData7.key310, by decide, canonicalPose7_310, canonicalMatch7_310, indexedKeyDecode7_310⟩
  · exact ⟨⟨272, by decide⟩, IndexedData7.key311, by decide, canonicalPose7_311, canonicalMatch7_311, indexedKeyDecode7_311⟩
  · exact ⟨⟨273, by decide⟩, IndexedData7.key312, by decide, canonicalPose7_312, canonicalMatch7_312, indexedKeyDecode7_312⟩
  · exact ⟨⟨274, by decide⟩, IndexedData7.key313, by decide, canonicalPose7_313, canonicalMatch7_313, indexedKeyDecode7_313⟩
  · exact ⟨⟨275, by decide⟩, IndexedData7.key314, by decide, canonicalPose7_314, canonicalMatch7_314, indexedKeyDecode7_314⟩
  · exact ⟨⟨276, by decide⟩, IndexedData7.key315, by decide, canonicalPose7_315, canonicalMatch7_315, indexedKeyDecode7_315⟩
  · exact ⟨⟨277, by decide⟩, IndexedData7.key316, by decide, canonicalPose7_316, canonicalMatch7_316, indexedKeyDecode7_316⟩
  · exact ⟨⟨277, by decide⟩, IndexedData7.key317, by decide, canonicalPose7_317, canonicalMatch7_317, indexedKeyDecode7_317⟩
  · exact ⟨⟨278, by decide⟩, IndexedData7.key318, by decide, canonicalPose7_318, canonicalMatch7_318, indexedKeyDecode7_318⟩
  · exact ⟨⟨279, by decide⟩, IndexedData7.key319, by decide, canonicalPose7_319, canonicalMatch7_319, indexedKeyDecode7_319⟩

#print axioms keys7Chunk9_aligned

end SparseMonotiles.Canonical
