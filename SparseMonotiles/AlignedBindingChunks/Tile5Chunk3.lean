module

public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk3

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys5Chunk3_aligned : ∀ k ∈ keys5Chunk3,
    ∃ i : Fin 160, ∃ b ∈ IndexedData5.geometry.profile i, ∃ p : Pose 5,
      p.boxKey 19200 (referenceBox5 (!b.bump)) = b ∧ b.toKeyData 19200 = k := by
  intro k hk
  simp only [keys5Chunk3, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨60, by decide⟩, IndexedData5.key96, by decide, canonicalPose5_96, canonicalMatch5_96, indexedKeyDecode5_96⟩
  · exact ⟨⟨61, by decide⟩, IndexedData5.key97, by decide, canonicalPose5_97, canonicalMatch5_97, indexedKeyDecode5_97⟩
  · exact ⟨⟨62, by decide⟩, IndexedData5.key98, by decide, canonicalPose5_98, canonicalMatch5_98, indexedKeyDecode5_98⟩
  · exact ⟨⟨63, by decide⟩, IndexedData5.key99, by decide, canonicalPose5_99, canonicalMatch5_99, indexedKeyDecode5_99⟩
  · exact ⟨⟨64, by decide⟩, IndexedData5.key100, by decide, canonicalPose5_100, canonicalMatch5_100, indexedKeyDecode5_100⟩
  · exact ⟨⟨64, by decide⟩, IndexedData5.key101, by decide, canonicalPose5_101, canonicalMatch5_101, indexedKeyDecode5_101⟩
  · exact ⟨⟨64, by decide⟩, IndexedData5.key102, by decide, canonicalPose5_102, canonicalMatch5_102, indexedKeyDecode5_102⟩
  · exact ⟨⟨64, by decide⟩, IndexedData5.key103, by decide, canonicalPose5_103, canonicalMatch5_103, indexedKeyDecode5_103⟩
  · exact ⟨⟨65, by decide⟩, IndexedData5.key104, by decide, canonicalPose5_104, canonicalMatch5_104, indexedKeyDecode5_104⟩
  · exact ⟨⟨66, by decide⟩, IndexedData5.key105, by decide, canonicalPose5_105, canonicalMatch5_105, indexedKeyDecode5_105⟩
  · exact ⟨⟨67, by decide⟩, IndexedData5.key106, by decide, canonicalPose5_106, canonicalMatch5_106, indexedKeyDecode5_106⟩
  · exact ⟨⟨68, by decide⟩, IndexedData5.key107, by decide, canonicalPose5_107, canonicalMatch5_107, indexedKeyDecode5_107⟩
  · exact ⟨⟨69, by decide⟩, IndexedData5.key108, by decide, canonicalPose5_108, canonicalMatch5_108, indexedKeyDecode5_108⟩
  · exact ⟨⟨69, by decide⟩, IndexedData5.key109, by decide, canonicalPose5_109, canonicalMatch5_109, indexedKeyDecode5_109⟩
  · exact ⟨⟨69, by decide⟩, IndexedData5.key110, by decide, canonicalPose5_110, canonicalMatch5_110, indexedKeyDecode5_110⟩
  · exact ⟨⟨69, by decide⟩, IndexedData5.key111, by decide, canonicalPose5_111, canonicalMatch5_111, indexedKeyDecode5_111⟩
  · exact ⟨⟨70, by decide⟩, IndexedData5.key112, by decide, canonicalPose5_112, canonicalMatch5_112, indexedKeyDecode5_112⟩
  · exact ⟨⟨71, by decide⟩, IndexedData5.key113, by decide, canonicalPose5_113, canonicalMatch5_113, indexedKeyDecode5_113⟩
  · exact ⟨⟨72, by decide⟩, IndexedData5.key114, by decide, canonicalPose5_114, canonicalMatch5_114, indexedKeyDecode5_114⟩
  · exact ⟨⟨72, by decide⟩, IndexedData5.key115, by decide, canonicalPose5_115, canonicalMatch5_115, indexedKeyDecode5_115⟩
  · exact ⟨⟨72, by decide⟩, IndexedData5.key116, by decide, canonicalPose5_116, canonicalMatch5_116, indexedKeyDecode5_116⟩
  · exact ⟨⟨72, by decide⟩, IndexedData5.key117, by decide, canonicalPose5_117, canonicalMatch5_117, indexedKeyDecode5_117⟩
  · exact ⟨⟨73, by decide⟩, IndexedData5.key118, by decide, canonicalPose5_118, canonicalMatch5_118, indexedKeyDecode5_118⟩
  · exact ⟨⟨74, by decide⟩, IndexedData5.key119, by decide, canonicalPose5_119, canonicalMatch5_119, indexedKeyDecode5_119⟩
  · exact ⟨⟨75, by decide⟩, IndexedData5.key120, by decide, canonicalPose5_120, canonicalMatch5_120, indexedKeyDecode5_120⟩
  · exact ⟨⟨75, by decide⟩, IndexedData5.key121, by decide, canonicalPose5_121, canonicalMatch5_121, indexedKeyDecode5_121⟩
  · exact ⟨⟨75, by decide⟩, IndexedData5.key122, by decide, canonicalPose5_122, canonicalMatch5_122, indexedKeyDecode5_122⟩
  · exact ⟨⟨75, by decide⟩, IndexedData5.key123, by decide, canonicalPose5_123, canonicalMatch5_123, indexedKeyDecode5_123⟩
  · exact ⟨⟨76, by decide⟩, IndexedData5.key124, by decide, canonicalPose5_124, canonicalMatch5_124, indexedKeyDecode5_124⟩
  · exact ⟨⟨76, by decide⟩, IndexedData5.key125, by decide, canonicalPose5_125, canonicalMatch5_125, indexedKeyDecode5_125⟩
  · exact ⟨⟨76, by decide⟩, IndexedData5.key126, by decide, canonicalPose5_126, canonicalMatch5_126, indexedKeyDecode5_126⟩
  · exact ⟨⟨76, by decide⟩, IndexedData5.key127, by decide, canonicalPose5_127, canonicalMatch5_127, indexedKeyDecode5_127⟩

#print axioms keys5Chunk3_aligned

end SparseMonotiles.Canonical
