module

public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk2

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys5Chunk2_aligned : ∀ k ∈ keys5Chunk2,
    ∃ i : Fin 160, ∃ b ∈ IndexedData5.geometry.profile i, ∃ p : Pose 5,
      p.boxKey 19200 (referenceBox5 (!b.bump)) = b ∧ b.toKeyData 19200 = k := by
  intro k hk
  simp only [keys5Chunk2, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨40, by decide⟩, IndexedData5.key64, by decide, canonicalPose5_64, canonicalMatch5_64, indexedKeyDecode5_64⟩
  · exact ⟨⟨41, by decide⟩, IndexedData5.key65, by decide, canonicalPose5_65, canonicalMatch5_65, indexedKeyDecode5_65⟩
  · exact ⟨⟨41, by decide⟩, IndexedData5.key66, by decide, canonicalPose5_66, canonicalMatch5_66, indexedKeyDecode5_66⟩
  · exact ⟨⟨41, by decide⟩, IndexedData5.key67, by decide, canonicalPose5_67, canonicalMatch5_67, indexedKeyDecode5_67⟩
  · exact ⟨⟨41, by decide⟩, IndexedData5.key68, by decide, canonicalPose5_68, canonicalMatch5_68, indexedKeyDecode5_68⟩
  · exact ⟨⟨42, by decide⟩, IndexedData5.key69, by decide, canonicalPose5_69, canonicalMatch5_69, indexedKeyDecode5_69⟩
  · exact ⟨⟨43, by decide⟩, IndexedData5.key70, by decide, canonicalPose5_70, canonicalMatch5_70, indexedKeyDecode5_70⟩
  · exact ⟨⟨44, by decide⟩, IndexedData5.key71, by decide, canonicalPose5_71, canonicalMatch5_71, indexedKeyDecode5_71⟩
  · exact ⟨⟨45, by decide⟩, IndexedData5.key72, by decide, canonicalPose5_72, canonicalMatch5_72, indexedKeyDecode5_72⟩
  · exact ⟨⟨45, by decide⟩, IndexedData5.key73, by decide, canonicalPose5_73, canonicalMatch5_73, indexedKeyDecode5_73⟩
  · exact ⟨⟨45, by decide⟩, IndexedData5.key74, by decide, canonicalPose5_74, canonicalMatch5_74, indexedKeyDecode5_74⟩
  · exact ⟨⟨45, by decide⟩, IndexedData5.key75, by decide, canonicalPose5_75, canonicalMatch5_75, indexedKeyDecode5_75⟩
  · exact ⟨⟨46, by decide⟩, IndexedData5.key76, by decide, canonicalPose5_76, canonicalMatch5_76, indexedKeyDecode5_76⟩
  · exact ⟨⟨47, by decide⟩, IndexedData5.key77, by decide, canonicalPose5_77, canonicalMatch5_77, indexedKeyDecode5_77⟩
  · exact ⟨⟨48, by decide⟩, IndexedData5.key78, by decide, canonicalPose5_78, canonicalMatch5_78, indexedKeyDecode5_78⟩
  · exact ⟨⟨49, by decide⟩, IndexedData5.key79, by decide, canonicalPose5_79, canonicalMatch5_79, indexedKeyDecode5_79⟩
  · exact ⟨⟨50, by decide⟩, IndexedData5.key80, by decide, canonicalPose5_80, canonicalMatch5_80, indexedKeyDecode5_80⟩
  · exact ⟨⟨51, by decide⟩, IndexedData5.key81, by decide, canonicalPose5_81, canonicalMatch5_81, indexedKeyDecode5_81⟩
  · exact ⟨⟨52, by decide⟩, IndexedData5.key82, by decide, canonicalPose5_82, canonicalMatch5_82, indexedKeyDecode5_82⟩
  · exact ⟨⟨52, by decide⟩, IndexedData5.key83, by decide, canonicalPose5_83, canonicalMatch5_83, indexedKeyDecode5_83⟩
  · exact ⟨⟨52, by decide⟩, IndexedData5.key84, by decide, canonicalPose5_84, canonicalMatch5_84, indexedKeyDecode5_84⟩
  · exact ⟨⟨52, by decide⟩, IndexedData5.key85, by decide, canonicalPose5_85, canonicalMatch5_85, indexedKeyDecode5_85⟩
  · exact ⟨⟨53, by decide⟩, IndexedData5.key86, by decide, canonicalPose5_86, canonicalMatch5_86, indexedKeyDecode5_86⟩
  · exact ⟨⟨54, by decide⟩, IndexedData5.key87, by decide, canonicalPose5_87, canonicalMatch5_87, indexedKeyDecode5_87⟩
  · exact ⟨⟨55, by decide⟩, IndexedData5.key88, by decide, canonicalPose5_88, canonicalMatch5_88, indexedKeyDecode5_88⟩
  · exact ⟨⟨56, by decide⟩, IndexedData5.key89, by decide, canonicalPose5_89, canonicalMatch5_89, indexedKeyDecode5_89⟩
  · exact ⟨⟨56, by decide⟩, IndexedData5.key90, by decide, canonicalPose5_90, canonicalMatch5_90, indexedKeyDecode5_90⟩
  · exact ⟨⟨56, by decide⟩, IndexedData5.key91, by decide, canonicalPose5_91, canonicalMatch5_91, indexedKeyDecode5_91⟩
  · exact ⟨⟨56, by decide⟩, IndexedData5.key92, by decide, canonicalPose5_92, canonicalMatch5_92, indexedKeyDecode5_92⟩
  · exact ⟨⟨57, by decide⟩, IndexedData5.key93, by decide, canonicalPose5_93, canonicalMatch5_93, indexedKeyDecode5_93⟩
  · exact ⟨⟨58, by decide⟩, IndexedData5.key94, by decide, canonicalPose5_94, canonicalMatch5_94, indexedKeyDecode5_94⟩
  · exact ⟨⟨59, by decide⟩, IndexedData5.key95, by decide, canonicalPose5_95, canonicalMatch5_95, indexedKeyDecode5_95⟩

#print axioms keys5Chunk2_aligned

end SparseMonotiles.Canonical
