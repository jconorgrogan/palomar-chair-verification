module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk3

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk3_aligned : ∀ k ∈ keys7Chunk3,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk3, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨84, by decide⟩, IndexedData7.key96, by decide, canonicalPose7_96, canonicalMatch7_96, indexedKeyDecode7_96⟩
  · exact ⟨⟨84, by decide⟩, IndexedData7.key97, by decide, canonicalPose7_97, canonicalMatch7_97, indexedKeyDecode7_97⟩
  · exact ⟨⟨85, by decide⟩, IndexedData7.key98, by decide, canonicalPose7_98, canonicalMatch7_98, indexedKeyDecode7_98⟩
  · exact ⟨⟨86, by decide⟩, IndexedData7.key99, by decide, canonicalPose7_99, canonicalMatch7_99, indexedKeyDecode7_99⟩
  · exact ⟨⟨87, by decide⟩, IndexedData7.key100, by decide, canonicalPose7_100, canonicalMatch7_100, indexedKeyDecode7_100⟩
  · exact ⟨⟨88, by decide⟩, IndexedData7.key101, by decide, canonicalPose7_101, canonicalMatch7_101, indexedKeyDecode7_101⟩
  · exact ⟨⟨89, by decide⟩, IndexedData7.key102, by decide, canonicalPose7_102, canonicalMatch7_102, indexedKeyDecode7_102⟩
  · exact ⟨⟨90, by decide⟩, IndexedData7.key103, by decide, canonicalPose7_103, canonicalMatch7_103, indexedKeyDecode7_103⟩
  · exact ⟨⟨91, by decide⟩, IndexedData7.key104, by decide, canonicalPose7_104, canonicalMatch7_104, indexedKeyDecode7_104⟩
  · exact ⟨⟨92, by decide⟩, IndexedData7.key105, by decide, canonicalPose7_105, canonicalMatch7_105, indexedKeyDecode7_105⟩
  · exact ⟨⟨93, by decide⟩, IndexedData7.key106, by decide, canonicalPose7_106, canonicalMatch7_106, indexedKeyDecode7_106⟩
  · exact ⟨⟨93, by decide⟩, IndexedData7.key107, by decide, canonicalPose7_107, canonicalMatch7_107, indexedKeyDecode7_107⟩
  · exact ⟨⟨94, by decide⟩, IndexedData7.key108, by decide, canonicalPose7_108, canonicalMatch7_108, indexedKeyDecode7_108⟩
  · exact ⟨⟨95, by decide⟩, IndexedData7.key109, by decide, canonicalPose7_109, canonicalMatch7_109, indexedKeyDecode7_109⟩
  · exact ⟨⟨96, by decide⟩, IndexedData7.key110, by decide, canonicalPose7_110, canonicalMatch7_110, indexedKeyDecode7_110⟩
  · exact ⟨⟨97, by decide⟩, IndexedData7.key111, by decide, canonicalPose7_111, canonicalMatch7_111, indexedKeyDecode7_111⟩
  · exact ⟨⟨98, by decide⟩, IndexedData7.key112, by decide, canonicalPose7_112, canonicalMatch7_112, indexedKeyDecode7_112⟩
  · exact ⟨⟨99, by decide⟩, IndexedData7.key113, by decide, canonicalPose7_113, canonicalMatch7_113, indexedKeyDecode7_113⟩
  · exact ⟨⟨100, by decide⟩, IndexedData7.key114, by decide, canonicalPose7_114, canonicalMatch7_114, indexedKeyDecode7_114⟩
  · exact ⟨⟨101, by decide⟩, IndexedData7.key115, by decide, canonicalPose7_115, canonicalMatch7_115, indexedKeyDecode7_115⟩
  · exact ⟨⟨102, by decide⟩, IndexedData7.key116, by decide, canonicalPose7_116, canonicalMatch7_116, indexedKeyDecode7_116⟩
  · exact ⟨⟨102, by decide⟩, IndexedData7.key117, by decide, canonicalPose7_117, canonicalMatch7_117, indexedKeyDecode7_117⟩
  · exact ⟨⟨103, by decide⟩, IndexedData7.key118, by decide, canonicalPose7_118, canonicalMatch7_118, indexedKeyDecode7_118⟩
  · exact ⟨⟨104, by decide⟩, IndexedData7.key119, by decide, canonicalPose7_119, canonicalMatch7_119, indexedKeyDecode7_119⟩
  · exact ⟨⟨105, by decide⟩, IndexedData7.key120, by decide, canonicalPose7_120, canonicalMatch7_120, indexedKeyDecode7_120⟩
  · exact ⟨⟨106, by decide⟩, IndexedData7.key121, by decide, canonicalPose7_121, canonicalMatch7_121, indexedKeyDecode7_121⟩
  · exact ⟨⟨106, by decide⟩, IndexedData7.key122, by decide, canonicalPose7_122, canonicalMatch7_122, indexedKeyDecode7_122⟩
  · exact ⟨⟨107, by decide⟩, IndexedData7.key123, by decide, canonicalPose7_123, canonicalMatch7_123, indexedKeyDecode7_123⟩
  · exact ⟨⟨108, by decide⟩, IndexedData7.key124, by decide, canonicalPose7_124, canonicalMatch7_124, indexedKeyDecode7_124⟩
  · exact ⟨⟨109, by decide⟩, IndexedData7.key125, by decide, canonicalPose7_125, canonicalMatch7_125, indexedKeyDecode7_125⟩
  · exact ⟨⟨110, by decide⟩, IndexedData7.key126, by decide, canonicalPose7_126, canonicalMatch7_126, indexedKeyDecode7_126⟩
  · exact ⟨⟨111, by decide⟩, IndexedData7.key127, by decide, canonicalPose7_127, canonicalMatch7_127, indexedKeyDecode7_127⟩

#print axioms keys7Chunk3_aligned

end SparseMonotiles.Canonical
