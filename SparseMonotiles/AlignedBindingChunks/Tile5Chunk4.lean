module

public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk4

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys5Chunk4_aligned : ∀ k ∈ keys5Chunk4,
    ∃ i : Fin 160, ∃ b ∈ IndexedData5.geometry.profile i, ∃ p : Pose 5,
      p.boxKey 19200 (referenceBox5 (!b.bump)) = b ∧ b.toKeyData 19200 = k := by
  intro k hk
  simp only [keys5Chunk4, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨77, by decide⟩, IndexedData5.key128, by decide, canonicalPose5_128, canonicalMatch5_128, indexedKeyDecode5_128⟩
  · exact ⟨⟨78, by decide⟩, IndexedData5.key129, by decide, canonicalPose5_129, canonicalMatch5_129, indexedKeyDecode5_129⟩
  · exact ⟨⟨79, by decide⟩, IndexedData5.key130, by decide, canonicalPose5_130, canonicalMatch5_130, indexedKeyDecode5_130⟩
  · exact ⟨⟨80, by decide⟩, IndexedData5.key131, by decide, canonicalPose5_131, canonicalMatch5_131, indexedKeyDecode5_131⟩
  · exact ⟨⟨81, by decide⟩, IndexedData5.key132, by decide, canonicalPose5_132, canonicalMatch5_132, indexedKeyDecode5_132⟩
  · exact ⟨⟨81, by decide⟩, IndexedData5.key133, by decide, canonicalPose5_133, canonicalMatch5_133, indexedKeyDecode5_133⟩
  · exact ⟨⟨81, by decide⟩, IndexedData5.key134, by decide, canonicalPose5_134, canonicalMatch5_134, indexedKeyDecode5_134⟩
  · exact ⟨⟨81, by decide⟩, IndexedData5.key135, by decide, canonicalPose5_135, canonicalMatch5_135, indexedKeyDecode5_135⟩
  · exact ⟨⟨82, by decide⟩, IndexedData5.key136, by decide, canonicalPose5_136, canonicalMatch5_136, indexedKeyDecode5_136⟩
  · exact ⟨⟨83, by decide⟩, IndexedData5.key137, by decide, canonicalPose5_137, canonicalMatch5_137, indexedKeyDecode5_137⟩
  · exact ⟨⟨84, by decide⟩, IndexedData5.key138, by decide, canonicalPose5_138, canonicalMatch5_138, indexedKeyDecode5_138⟩
  · exact ⟨⟨85, by decide⟩, IndexedData5.key139, by decide, canonicalPose5_139, canonicalMatch5_139, indexedKeyDecode5_139⟩
  · exact ⟨⟨86, by decide⟩, IndexedData5.key140, by decide, canonicalPose5_140, canonicalMatch5_140, indexedKeyDecode5_140⟩
  · exact ⟨⟨87, by decide⟩, IndexedData5.key141, by decide, canonicalPose5_141, canonicalMatch5_141, indexedKeyDecode5_141⟩
  · exact ⟨⟨88, by decide⟩, IndexedData5.key142, by decide, canonicalPose5_142, canonicalMatch5_142, indexedKeyDecode5_142⟩
  · exact ⟨⟨88, by decide⟩, IndexedData5.key143, by decide, canonicalPose5_143, canonicalMatch5_143, indexedKeyDecode5_143⟩
  · exact ⟨⟨88, by decide⟩, IndexedData5.key144, by decide, canonicalPose5_144, canonicalMatch5_144, indexedKeyDecode5_144⟩
  · exact ⟨⟨88, by decide⟩, IndexedData5.key145, by decide, canonicalPose5_145, canonicalMatch5_145, indexedKeyDecode5_145⟩
  · exact ⟨⟨89, by decide⟩, IndexedData5.key146, by decide, canonicalPose5_146, canonicalMatch5_146, indexedKeyDecode5_146⟩
  · exact ⟨⟨90, by decide⟩, IndexedData5.key147, by decide, canonicalPose5_147, canonicalMatch5_147, indexedKeyDecode5_147⟩
  · exact ⟨⟨91, by decide⟩, IndexedData5.key148, by decide, canonicalPose5_148, canonicalMatch5_148, indexedKeyDecode5_148⟩
  · exact ⟨⟨92, by decide⟩, IndexedData5.key149, by decide, canonicalPose5_149, canonicalMatch5_149, indexedKeyDecode5_149⟩
  · exact ⟨⟨93, by decide⟩, IndexedData5.key150, by decide, canonicalPose5_150, canonicalMatch5_150, indexedKeyDecode5_150⟩
  · exact ⟨⟨94, by decide⟩, IndexedData5.key151, by decide, canonicalPose5_151, canonicalMatch5_151, indexedKeyDecode5_151⟩
  · exact ⟨⟨95, by decide⟩, IndexedData5.key152, by decide, canonicalPose5_152, canonicalMatch5_152, indexedKeyDecode5_152⟩
  · exact ⟨⟨95, by decide⟩, IndexedData5.key153, by decide, canonicalPose5_153, canonicalMatch5_153, indexedKeyDecode5_153⟩
  · exact ⟨⟨95, by decide⟩, IndexedData5.key154, by decide, canonicalPose5_154, canonicalMatch5_154, indexedKeyDecode5_154⟩
  · exact ⟨⟨95, by decide⟩, IndexedData5.key155, by decide, canonicalPose5_155, canonicalMatch5_155, indexedKeyDecode5_155⟩
  · exact ⟨⟨96, by decide⟩, IndexedData5.key156, by decide, canonicalPose5_156, canonicalMatch5_156, indexedKeyDecode5_156⟩
  · exact ⟨⟨97, by decide⟩, IndexedData5.key157, by decide, canonicalPose5_157, canonicalMatch5_157, indexedKeyDecode5_157⟩
  · exact ⟨⟨98, by decide⟩, IndexedData5.key158, by decide, canonicalPose5_158, canonicalMatch5_158, indexedKeyDecode5_158⟩
  · exact ⟨⟨99, by decide⟩, IndexedData5.key159, by decide, canonicalPose5_159, canonicalMatch5_159, indexedKeyDecode5_159⟩

#print axioms keys5Chunk4_aligned

end SparseMonotiles.Canonical
