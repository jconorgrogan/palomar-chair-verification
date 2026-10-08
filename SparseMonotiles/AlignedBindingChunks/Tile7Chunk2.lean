module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk2

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk2_aligned : ∀ k ∈ keys7Chunk2,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk2, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨56, by decide⟩, IndexedData7.key64, by decide, canonicalPose7_64, canonicalMatch7_64, indexedKeyDecode7_64⟩
  · exact ⟨⟨57, by decide⟩, IndexedData7.key65, by decide, canonicalPose7_65, canonicalMatch7_65, indexedKeyDecode7_65⟩
  · exact ⟨⟨58, by decide⟩, IndexedData7.key66, by decide, canonicalPose7_66, canonicalMatch7_66, indexedKeyDecode7_66⟩
  · exact ⟨⟨59, by decide⟩, IndexedData7.key67, by decide, canonicalPose7_67, canonicalMatch7_67, indexedKeyDecode7_67⟩
  · exact ⟨⟨59, by decide⟩, IndexedData7.key68, by decide, canonicalPose7_68, canonicalMatch7_68, indexedKeyDecode7_68⟩
  · exact ⟨⟨60, by decide⟩, IndexedData7.key69, by decide, canonicalPose7_69, canonicalMatch7_69, indexedKeyDecode7_69⟩
  · exact ⟨⟨61, by decide⟩, IndexedData7.key70, by decide, canonicalPose7_70, canonicalMatch7_70, indexedKeyDecode7_70⟩
  · exact ⟨⟨62, by decide⟩, IndexedData7.key71, by decide, canonicalPose7_71, canonicalMatch7_71, indexedKeyDecode7_71⟩
  · exact ⟨⟨63, by decide⟩, IndexedData7.key72, by decide, canonicalPose7_72, canonicalMatch7_72, indexedKeyDecode7_72⟩
  · exact ⟨⟨64, by decide⟩, IndexedData7.key73, by decide, canonicalPose7_73, canonicalMatch7_73, indexedKeyDecode7_73⟩
  · exact ⟨⟨64, by decide⟩, IndexedData7.key74, by decide, canonicalPose7_74, canonicalMatch7_74, indexedKeyDecode7_74⟩
  · exact ⟨⟨65, by decide⟩, IndexedData7.key75, by decide, canonicalPose7_75, canonicalMatch7_75, indexedKeyDecode7_75⟩
  · exact ⟨⟨66, by decide⟩, IndexedData7.key76, by decide, canonicalPose7_76, canonicalMatch7_76, indexedKeyDecode7_76⟩
  · exact ⟨⟨67, by decide⟩, IndexedData7.key77, by decide, canonicalPose7_77, canonicalMatch7_77, indexedKeyDecode7_77⟩
  · exact ⟨⟨68, by decide⟩, IndexedData7.key78, by decide, canonicalPose7_78, canonicalMatch7_78, indexedKeyDecode7_78⟩
  · exact ⟨⟨69, by decide⟩, IndexedData7.key79, by decide, canonicalPose7_79, canonicalMatch7_79, indexedKeyDecode7_79⟩
  · exact ⟨⟨70, by decide⟩, IndexedData7.key80, by decide, canonicalPose7_80, canonicalMatch7_80, indexedKeyDecode7_80⟩
  · exact ⟨⟨71, by decide⟩, IndexedData7.key81, by decide, canonicalPose7_81, canonicalMatch7_81, indexedKeyDecode7_81⟩
  · exact ⟨⟨72, by decide⟩, IndexedData7.key82, by decide, canonicalPose7_82, canonicalMatch7_82, indexedKeyDecode7_82⟩
  · exact ⟨⟨73, by decide⟩, IndexedData7.key83, by decide, canonicalPose7_83, canonicalMatch7_83, indexedKeyDecode7_83⟩
  · exact ⟨⟨74, by decide⟩, IndexedData7.key84, by decide, canonicalPose7_84, canonicalMatch7_84, indexedKeyDecode7_84⟩
  · exact ⟨⟨74, by decide⟩, IndexedData7.key85, by decide, canonicalPose7_85, canonicalMatch7_85, indexedKeyDecode7_85⟩
  · exact ⟨⟨75, by decide⟩, IndexedData7.key86, by decide, canonicalPose7_86, canonicalMatch7_86, indexedKeyDecode7_86⟩
  · exact ⟨⟨76, by decide⟩, IndexedData7.key87, by decide, canonicalPose7_87, canonicalMatch7_87, indexedKeyDecode7_87⟩
  · exact ⟨⟨77, by decide⟩, IndexedData7.key88, by decide, canonicalPose7_88, canonicalMatch7_88, indexedKeyDecode7_88⟩
  · exact ⟨⟨77, by decide⟩, IndexedData7.key89, by decide, canonicalPose7_89, canonicalMatch7_89, indexedKeyDecode7_89⟩
  · exact ⟨⟨78, by decide⟩, IndexedData7.key90, by decide, canonicalPose7_90, canonicalMatch7_90, indexedKeyDecode7_90⟩
  · exact ⟨⟨79, by decide⟩, IndexedData7.key91, by decide, canonicalPose7_91, canonicalMatch7_91, indexedKeyDecode7_91⟩
  · exact ⟨⟨80, by decide⟩, IndexedData7.key92, by decide, canonicalPose7_92, canonicalMatch7_92, indexedKeyDecode7_92⟩
  · exact ⟨⟨81, by decide⟩, IndexedData7.key93, by decide, canonicalPose7_93, canonicalMatch7_93, indexedKeyDecode7_93⟩
  · exact ⟨⟨82, by decide⟩, IndexedData7.key94, by decide, canonicalPose7_94, canonicalMatch7_94, indexedKeyDecode7_94⟩
  · exact ⟨⟨83, by decide⟩, IndexedData7.key95, by decide, canonicalPose7_95, canonicalMatch7_95, indexedKeyDecode7_95⟩

#print axioms keys7Chunk2_aligned

end SparseMonotiles.Canonical
