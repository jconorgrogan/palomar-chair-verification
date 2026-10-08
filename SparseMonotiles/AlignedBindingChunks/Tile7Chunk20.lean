module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk20

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk20_aligned : ∀ k ∈ keys7Chunk20,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk20, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨559, by decide⟩, IndexedData7.key640, by decide, canonicalPose7_640, canonicalMatch7_640, indexedKeyDecode7_640⟩
  · exact ⟨⟨560, by decide⟩, IndexedData7.key641, by decide, canonicalPose7_641, canonicalMatch7_641, indexedKeyDecode7_641⟩
  · exact ⟨⟨561, by decide⟩, IndexedData7.key642, by decide, canonicalPose7_642, canonicalMatch7_642, indexedKeyDecode7_642⟩
  · exact ⟨⟨562, by decide⟩, IndexedData7.key643, by decide, canonicalPose7_643, canonicalMatch7_643, indexedKeyDecode7_643⟩
  · exact ⟨⟨562, by decide⟩, IndexedData7.key644, by decide, canonicalPose7_644, canonicalMatch7_644, indexedKeyDecode7_644⟩
  · exact ⟨⟨563, by decide⟩, IndexedData7.key645, by decide, canonicalPose7_645, canonicalMatch7_645, indexedKeyDecode7_645⟩
  · exact ⟨⟨564, by decide⟩, IndexedData7.key646, by decide, canonicalPose7_646, canonicalMatch7_646, indexedKeyDecode7_646⟩
  · exact ⟨⟨565, by decide⟩, IndexedData7.key647, by decide, canonicalPose7_647, canonicalMatch7_647, indexedKeyDecode7_647⟩
  · exact ⟨⟨566, by decide⟩, IndexedData7.key648, by decide, canonicalPose7_648, canonicalMatch7_648, indexedKeyDecode7_648⟩
  · exact ⟨⟨567, by decide⟩, IndexedData7.key649, by decide, canonicalPose7_649, canonicalMatch7_649, indexedKeyDecode7_649⟩
  · exact ⟨⟨568, by decide⟩, IndexedData7.key650, by decide, canonicalPose7_650, canonicalMatch7_650, indexedKeyDecode7_650⟩
  · exact ⟨⟨569, by decide⟩, IndexedData7.key651, by decide, canonicalPose7_651, canonicalMatch7_651, indexedKeyDecode7_651⟩
  · exact ⟨⟨570, by decide⟩, IndexedData7.key652, by decide, canonicalPose7_652, canonicalMatch7_652, indexedKeyDecode7_652⟩
  · exact ⟨⟨571, by decide⟩, IndexedData7.key653, by decide, canonicalPose7_653, canonicalMatch7_653, indexedKeyDecode7_653⟩
  · exact ⟨⟨572, by decide⟩, IndexedData7.key654, by decide, canonicalPose7_654, canonicalMatch7_654, indexedKeyDecode7_654⟩
  · exact ⟨⟨573, by decide⟩, IndexedData7.key655, by decide, canonicalPose7_655, canonicalMatch7_655, indexedKeyDecode7_655⟩
  · exact ⟨⟨573, by decide⟩, IndexedData7.key656, by decide, canonicalPose7_656, canonicalMatch7_656, indexedKeyDecode7_656⟩
  · exact ⟨⟨574, by decide⟩, IndexedData7.key657, by decide, canonicalPose7_657, canonicalMatch7_657, indexedKeyDecode7_657⟩
  · exact ⟨⟨575, by decide⟩, IndexedData7.key658, by decide, canonicalPose7_658, canonicalMatch7_658, indexedKeyDecode7_658⟩
  · exact ⟨⟨575, by decide⟩, IndexedData7.key659, by decide, canonicalPose7_659, canonicalMatch7_659, indexedKeyDecode7_659⟩
  · exact ⟨⟨576, by decide⟩, IndexedData7.key660, by decide, canonicalPose7_660, canonicalMatch7_660, indexedKeyDecode7_660⟩
  · exact ⟨⟨577, by decide⟩, IndexedData7.key661, by decide, canonicalPose7_661, canonicalMatch7_661, indexedKeyDecode7_661⟩
  · exact ⟨⟨578, by decide⟩, IndexedData7.key662, by decide, canonicalPose7_662, canonicalMatch7_662, indexedKeyDecode7_662⟩
  · exact ⟨⟨579, by decide⟩, IndexedData7.key663, by decide, canonicalPose7_663, canonicalMatch7_663, indexedKeyDecode7_663⟩
  · exact ⟨⟨580, by decide⟩, IndexedData7.key664, by decide, canonicalPose7_664, canonicalMatch7_664, indexedKeyDecode7_664⟩
  · exact ⟨⟨581, by decide⟩, IndexedData7.key665, by decide, canonicalPose7_665, canonicalMatch7_665, indexedKeyDecode7_665⟩
  · exact ⟨⟨582, by decide⟩, IndexedData7.key666, by decide, canonicalPose7_666, canonicalMatch7_666, indexedKeyDecode7_666⟩
  · exact ⟨⟨583, by decide⟩, IndexedData7.key667, by decide, canonicalPose7_667, canonicalMatch7_667, indexedKeyDecode7_667⟩
  · exact ⟨⟨584, by decide⟩, IndexedData7.key668, by decide, canonicalPose7_668, canonicalMatch7_668, indexedKeyDecode7_668⟩
  · exact ⟨⟨585, by decide⟩, IndexedData7.key669, by decide, canonicalPose7_669, canonicalMatch7_669, indexedKeyDecode7_669⟩
  · exact ⟨⟨586, by decide⟩, IndexedData7.key670, by decide, canonicalPose7_670, canonicalMatch7_670, indexedKeyDecode7_670⟩
  · exact ⟨⟨587, by decide⟩, IndexedData7.key671, by decide, canonicalPose7_671, canonicalMatch7_671, indexedKeyDecode7_671⟩

#print axioms keys7Chunk20_aligned

end SparseMonotiles.Canonical
