module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk22

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk22_aligned : ∀ k ∈ keys7Chunk22,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk22, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨615, by decide⟩, IndexedData7.key704, by decide, canonicalPose7_704, canonicalMatch7_704, indexedKeyDecode7_704⟩
  · exact ⟨⟨616, by decide⟩, IndexedData7.key705, by decide, canonicalPose7_705, canonicalMatch7_705, indexedKeyDecode7_705⟩
  · exact ⟨⟨617, by decide⟩, IndexedData7.key706, by decide, canonicalPose7_706, canonicalMatch7_706, indexedKeyDecode7_706⟩
  · exact ⟨⟨618, by decide⟩, IndexedData7.key707, by decide, canonicalPose7_707, canonicalMatch7_707, indexedKeyDecode7_707⟩
  · exact ⟨⟨619, by decide⟩, IndexedData7.key708, by decide, canonicalPose7_708, canonicalMatch7_708, indexedKeyDecode7_708⟩
  · exact ⟨⟨620, by decide⟩, IndexedData7.key709, by decide, canonicalPose7_709, canonicalMatch7_709, indexedKeyDecode7_709⟩
  · exact ⟨⟨621, by decide⟩, IndexedData7.key710, by decide, canonicalPose7_710, canonicalMatch7_710, indexedKeyDecode7_710⟩
  · exact ⟨⟨621, by decide⟩, IndexedData7.key711, by decide, canonicalPose7_711, canonicalMatch7_711, indexedKeyDecode7_711⟩
  · exact ⟨⟨622, by decide⟩, IndexedData7.key712, by decide, canonicalPose7_712, canonicalMatch7_712, indexedKeyDecode7_712⟩
  · exact ⟨⟨623, by decide⟩, IndexedData7.key713, by decide, canonicalPose7_713, canonicalMatch7_713, indexedKeyDecode7_713⟩
  · exact ⟨⟨624, by decide⟩, IndexedData7.key714, by decide, canonicalPose7_714, canonicalMatch7_714, indexedKeyDecode7_714⟩
  · exact ⟨⟨625, by decide⟩, IndexedData7.key715, by decide, canonicalPose7_715, canonicalMatch7_715, indexedKeyDecode7_715⟩
  · exact ⟨⟨625, by decide⟩, IndexedData7.key716, by decide, canonicalPose7_716, canonicalMatch7_716, indexedKeyDecode7_716⟩
  · exact ⟨⟨626, by decide⟩, IndexedData7.key717, by decide, canonicalPose7_717, canonicalMatch7_717, indexedKeyDecode7_717⟩
  · exact ⟨⟨627, by decide⟩, IndexedData7.key718, by decide, canonicalPose7_718, canonicalMatch7_718, indexedKeyDecode7_718⟩
  · exact ⟨⟨628, by decide⟩, IndexedData7.key719, by decide, canonicalPose7_719, canonicalMatch7_719, indexedKeyDecode7_719⟩
  · exact ⟨⟨629, by decide⟩, IndexedData7.key720, by decide, canonicalPose7_720, canonicalMatch7_720, indexedKeyDecode7_720⟩
  · exact ⟨⟨630, by decide⟩, IndexedData7.key721, by decide, canonicalPose7_721, canonicalMatch7_721, indexedKeyDecode7_721⟩
  · exact ⟨⟨631, by decide⟩, IndexedData7.key722, by decide, canonicalPose7_722, canonicalMatch7_722, indexedKeyDecode7_722⟩
  · exact ⟨⟨632, by decide⟩, IndexedData7.key723, by decide, canonicalPose7_723, canonicalMatch7_723, indexedKeyDecode7_723⟩
  · exact ⟨⟨633, by decide⟩, IndexedData7.key724, by decide, canonicalPose7_724, canonicalMatch7_724, indexedKeyDecode7_724⟩
  · exact ⟨⟨634, by decide⟩, IndexedData7.key725, by decide, canonicalPose7_725, canonicalMatch7_725, indexedKeyDecode7_725⟩
  · exact ⟨⟨635, by decide⟩, IndexedData7.key726, by decide, canonicalPose7_726, canonicalMatch7_726, indexedKeyDecode7_726⟩
  · exact ⟨⟨636, by decide⟩, IndexedData7.key727, by decide, canonicalPose7_727, canonicalMatch7_727, indexedKeyDecode7_727⟩
  · exact ⟨⟨637, by decide⟩, IndexedData7.key728, by decide, canonicalPose7_728, canonicalMatch7_728, indexedKeyDecode7_728⟩
  · exact ⟨⟨637, by decide⟩, IndexedData7.key729, by decide, canonicalPose7_729, canonicalMatch7_729, indexedKeyDecode7_729⟩
  · exact ⟨⟨638, by decide⟩, IndexedData7.key730, by decide, canonicalPose7_730, canonicalMatch7_730, indexedKeyDecode7_730⟩
  · exact ⟨⟨639, by decide⟩, IndexedData7.key731, by decide, canonicalPose7_731, canonicalMatch7_731, indexedKeyDecode7_731⟩
  · exact ⟨⟨640, by decide⟩, IndexedData7.key732, by decide, canonicalPose7_732, canonicalMatch7_732, indexedKeyDecode7_732⟩
  · exact ⟨⟨641, by decide⟩, IndexedData7.key733, by decide, canonicalPose7_733, canonicalMatch7_733, indexedKeyDecode7_733⟩
  · exact ⟨⟨642, by decide⟩, IndexedData7.key734, by decide, canonicalPose7_734, canonicalMatch7_734, indexedKeyDecode7_734⟩
  · exact ⟨⟨643, by decide⟩, IndexedData7.key735, by decide, canonicalPose7_735, canonicalMatch7_735, indexedKeyDecode7_735⟩

#print axioms keys7Chunk22_aligned

end SparseMonotiles.Canonical
