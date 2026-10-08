module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk26

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk26_aligned : ∀ k ∈ keys7Chunk26,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk26, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨728, by decide⟩, IndexedData7.key832, by decide, canonicalPose7_832, canonicalMatch7_832, indexedKeyDecode7_832⟩
  · exact ⟨⟨729, by decide⟩, IndexedData7.key833, by decide, canonicalPose7_833, canonicalMatch7_833, indexedKeyDecode7_833⟩
  · exact ⟨⟨729, by decide⟩, IndexedData7.key834, by decide, canonicalPose7_834, canonicalMatch7_834, indexedKeyDecode7_834⟩
  · exact ⟨⟨730, by decide⟩, IndexedData7.key835, by decide, canonicalPose7_835, canonicalMatch7_835, indexedKeyDecode7_835⟩
  · exact ⟨⟨731, by decide⟩, IndexedData7.key836, by decide, canonicalPose7_836, canonicalMatch7_836, indexedKeyDecode7_836⟩
  · exact ⟨⟨732, by decide⟩, IndexedData7.key837, by decide, canonicalPose7_837, canonicalMatch7_837, indexedKeyDecode7_837⟩
  · exact ⟨⟨733, by decide⟩, IndexedData7.key838, by decide, canonicalPose7_838, canonicalMatch7_838, indexedKeyDecode7_838⟩
  · exact ⟨⟨734, by decide⟩, IndexedData7.key839, by decide, canonicalPose7_839, canonicalMatch7_839, indexedKeyDecode7_839⟩
  · exact ⟨⟨735, by decide⟩, IndexedData7.key840, by decide, canonicalPose7_840, canonicalMatch7_840, indexedKeyDecode7_840⟩
  · exact ⟨⟨736, by decide⟩, IndexedData7.key841, by decide, canonicalPose7_841, canonicalMatch7_841, indexedKeyDecode7_841⟩
  · exact ⟨⟨736, by decide⟩, IndexedData7.key842, by decide, canonicalPose7_842, canonicalMatch7_842, indexedKeyDecode7_842⟩
  · exact ⟨⟨737, by decide⟩, IndexedData7.key843, by decide, canonicalPose7_843, canonicalMatch7_843, indexedKeyDecode7_843⟩
  · exact ⟨⟨738, by decide⟩, IndexedData7.key844, by decide, canonicalPose7_844, canonicalMatch7_844, indexedKeyDecode7_844⟩
  · exact ⟨⟨739, by decide⟩, IndexedData7.key845, by decide, canonicalPose7_845, canonicalMatch7_845, indexedKeyDecode7_845⟩
  · exact ⟨⟨740, by decide⟩, IndexedData7.key846, by decide, canonicalPose7_846, canonicalMatch7_846, indexedKeyDecode7_846⟩
  · exact ⟨⟨741, by decide⟩, IndexedData7.key847, by decide, canonicalPose7_847, canonicalMatch7_847, indexedKeyDecode7_847⟩
  · exact ⟨⟨742, by decide⟩, IndexedData7.key848, by decide, canonicalPose7_848, canonicalMatch7_848, indexedKeyDecode7_848⟩
  · exact ⟨⟨743, by decide⟩, IndexedData7.key849, by decide, canonicalPose7_849, canonicalMatch7_849, indexedKeyDecode7_849⟩
  · exact ⟨⟨743, by decide⟩, IndexedData7.key850, by decide, canonicalPose7_850, canonicalMatch7_850, indexedKeyDecode7_850⟩
  · exact ⟨⟨744, by decide⟩, IndexedData7.key851, by decide, canonicalPose7_851, canonicalMatch7_851, indexedKeyDecode7_851⟩
  · exact ⟨⟨745, by decide⟩, IndexedData7.key852, by decide, canonicalPose7_852, canonicalMatch7_852, indexedKeyDecode7_852⟩
  · exact ⟨⟨746, by decide⟩, IndexedData7.key853, by decide, canonicalPose7_853, canonicalMatch7_853, indexedKeyDecode7_853⟩
  · exact ⟨⟨747, by decide⟩, IndexedData7.key854, by decide, canonicalPose7_854, canonicalMatch7_854, indexedKeyDecode7_854⟩
  · exact ⟨⟨748, by decide⟩, IndexedData7.key855, by decide, canonicalPose7_855, canonicalMatch7_855, indexedKeyDecode7_855⟩
  · exact ⟨⟨748, by decide⟩, IndexedData7.key856, by decide, canonicalPose7_856, canonicalMatch7_856, indexedKeyDecode7_856⟩
  · exact ⟨⟨749, by decide⟩, IndexedData7.key857, by decide, canonicalPose7_857, canonicalMatch7_857, indexedKeyDecode7_857⟩
  · exact ⟨⟨750, by decide⟩, IndexedData7.key858, by decide, canonicalPose7_858, canonicalMatch7_858, indexedKeyDecode7_858⟩
  · exact ⟨⟨751, by decide⟩, IndexedData7.key859, by decide, canonicalPose7_859, canonicalMatch7_859, indexedKeyDecode7_859⟩
  · exact ⟨⟨752, by decide⟩, IndexedData7.key860, by decide, canonicalPose7_860, canonicalMatch7_860, indexedKeyDecode7_860⟩
  · exact ⟨⟨753, by decide⟩, IndexedData7.key861, by decide, canonicalPose7_861, canonicalMatch7_861, indexedKeyDecode7_861⟩
  · exact ⟨⟨754, by decide⟩, IndexedData7.key862, by decide, canonicalPose7_862, canonicalMatch7_862, indexedKeyDecode7_862⟩
  · exact ⟨⟨754, by decide⟩, IndexedData7.key863, by decide, canonicalPose7_863, canonicalMatch7_863, indexedKeyDecode7_863⟩

#print axioms keys7Chunk26_aligned

end SparseMonotiles.Canonical
