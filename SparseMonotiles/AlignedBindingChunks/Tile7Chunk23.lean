module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk23

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk23_aligned : ∀ k ∈ keys7Chunk23,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk23, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨644, by decide⟩, IndexedData7.key736, by decide, canonicalPose7_736, canonicalMatch7_736, indexedKeyDecode7_736⟩
  · exact ⟨⟨644, by decide⟩, IndexedData7.key737, by decide, canonicalPose7_737, canonicalMatch7_737, indexedKeyDecode7_737⟩
  · exact ⟨⟨645, by decide⟩, IndexedData7.key738, by decide, canonicalPose7_738, canonicalMatch7_738, indexedKeyDecode7_738⟩
  · exact ⟨⟨646, by decide⟩, IndexedData7.key739, by decide, canonicalPose7_739, canonicalMatch7_739, indexedKeyDecode7_739⟩
  · exact ⟨⟨647, by decide⟩, IndexedData7.key740, by decide, canonicalPose7_740, canonicalMatch7_740, indexedKeyDecode7_740⟩
  · exact ⟨⟨648, by decide⟩, IndexedData7.key741, by decide, canonicalPose7_741, canonicalMatch7_741, indexedKeyDecode7_741⟩
  · exact ⟨⟨649, by decide⟩, IndexedData7.key742, by decide, canonicalPose7_742, canonicalMatch7_742, indexedKeyDecode7_742⟩
  · exact ⟨⟨649, by decide⟩, IndexedData7.key743, by decide, canonicalPose7_743, canonicalMatch7_743, indexedKeyDecode7_743⟩
  · exact ⟨⟨650, by decide⟩, IndexedData7.key744, by decide, canonicalPose7_744, canonicalMatch7_744, indexedKeyDecode7_744⟩
  · exact ⟨⟨651, by decide⟩, IndexedData7.key745, by decide, canonicalPose7_745, canonicalMatch7_745, indexedKeyDecode7_745⟩
  · exact ⟨⟨652, by decide⟩, IndexedData7.key746, by decide, canonicalPose7_746, canonicalMatch7_746, indexedKeyDecode7_746⟩
  · exact ⟨⟨653, by decide⟩, IndexedData7.key747, by decide, canonicalPose7_747, canonicalMatch7_747, indexedKeyDecode7_747⟩
  · exact ⟨⟨654, by decide⟩, IndexedData7.key748, by decide, canonicalPose7_748, canonicalMatch7_748, indexedKeyDecode7_748⟩
  · exact ⟨⟨655, by decide⟩, IndexedData7.key749, by decide, canonicalPose7_749, canonicalMatch7_749, indexedKeyDecode7_749⟩
  · exact ⟨⟨655, by decide⟩, IndexedData7.key750, by decide, canonicalPose7_750, canonicalMatch7_750, indexedKeyDecode7_750⟩
  · exact ⟨⟨656, by decide⟩, IndexedData7.key751, by decide, canonicalPose7_751, canonicalMatch7_751, indexedKeyDecode7_751⟩
  · exact ⟨⟨657, by decide⟩, IndexedData7.key752, by decide, canonicalPose7_752, canonicalMatch7_752, indexedKeyDecode7_752⟩
  · exact ⟨⟨658, by decide⟩, IndexedData7.key753, by decide, canonicalPose7_753, canonicalMatch7_753, indexedKeyDecode7_753⟩
  · exact ⟨⟨659, by decide⟩, IndexedData7.key754, by decide, canonicalPose7_754, canonicalMatch7_754, indexedKeyDecode7_754⟩
  · exact ⟨⟨659, by decide⟩, IndexedData7.key755, by decide, canonicalPose7_755, canonicalMatch7_755, indexedKeyDecode7_755⟩
  · exact ⟨⟨660, by decide⟩, IndexedData7.key756, by decide, canonicalPose7_756, canonicalMatch7_756, indexedKeyDecode7_756⟩
  · exact ⟨⟨661, by decide⟩, IndexedData7.key757, by decide, canonicalPose7_757, canonicalMatch7_757, indexedKeyDecode7_757⟩
  · exact ⟨⟨662, by decide⟩, IndexedData7.key758, by decide, canonicalPose7_758, canonicalMatch7_758, indexedKeyDecode7_758⟩
  · exact ⟨⟨663, by decide⟩, IndexedData7.key759, by decide, canonicalPose7_759, canonicalMatch7_759, indexedKeyDecode7_759⟩
  · exact ⟨⟨664, by decide⟩, IndexedData7.key760, by decide, canonicalPose7_760, canonicalMatch7_760, indexedKeyDecode7_760⟩
  · exact ⟨⟨665, by decide⟩, IndexedData7.key761, by decide, canonicalPose7_761, canonicalMatch7_761, indexedKeyDecode7_761⟩
  · exact ⟨⟨666, by decide⟩, IndexedData7.key762, by decide, canonicalPose7_762, canonicalMatch7_762, indexedKeyDecode7_762⟩
  · exact ⟨⟨667, by decide⟩, IndexedData7.key763, by decide, canonicalPose7_763, canonicalMatch7_763, indexedKeyDecode7_763⟩
  · exact ⟨⟨667, by decide⟩, IndexedData7.key764, by decide, canonicalPose7_764, canonicalMatch7_764, indexedKeyDecode7_764⟩
  · exact ⟨⟨668, by decide⟩, IndexedData7.key765, by decide, canonicalPose7_765, canonicalMatch7_765, indexedKeyDecode7_765⟩
  · exact ⟨⟨669, by decide⟩, IndexedData7.key766, by decide, canonicalPose7_766, canonicalMatch7_766, indexedKeyDecode7_766⟩
  · exact ⟨⟨670, by decide⟩, IndexedData7.key767, by decide, canonicalPose7_767, canonicalMatch7_767, indexedKeyDecode7_767⟩

#print axioms keys7Chunk23_aligned

end SparseMonotiles.Canonical
