module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk31

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk31_aligned : ∀ k ∈ keys7Chunk31,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk31, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨868, by decide⟩, IndexedData7.key992, by decide, canonicalPose7_992, canonicalMatch7_992, indexedKeyDecode7_992⟩
  · exact ⟨⟨869, by decide⟩, IndexedData7.key993, by decide, canonicalPose7_993, canonicalMatch7_993, indexedKeyDecode7_993⟩
  · exact ⟨⟨869, by decide⟩, IndexedData7.key994, by decide, canonicalPose7_994, canonicalMatch7_994, indexedKeyDecode7_994⟩
  · exact ⟨⟨870, by decide⟩, IndexedData7.key995, by decide, canonicalPose7_995, canonicalMatch7_995, indexedKeyDecode7_995⟩
  · exact ⟨⟨871, by decide⟩, IndexedData7.key996, by decide, canonicalPose7_996, canonicalMatch7_996, indexedKeyDecode7_996⟩
  · exact ⟨⟨872, by decide⟩, IndexedData7.key997, by decide, canonicalPose7_997, canonicalMatch7_997, indexedKeyDecode7_997⟩
  · exact ⟨⟨873, by decide⟩, IndexedData7.key998, by decide, canonicalPose7_998, canonicalMatch7_998, indexedKeyDecode7_998⟩
  · exact ⟨⟨874, by decide⟩, IndexedData7.key999, by decide, canonicalPose7_999, canonicalMatch7_999, indexedKeyDecode7_999⟩
  · exact ⟨⟨875, by decide⟩, IndexedData7.key1000, by decide, canonicalPose7_1000, canonicalMatch7_1000, indexedKeyDecode7_1000⟩
  · exact ⟨⟨875, by decide⟩, IndexedData7.key1001, by decide, canonicalPose7_1001, canonicalMatch7_1001, indexedKeyDecode7_1001⟩
  · exact ⟨⟨876, by decide⟩, IndexedData7.key1002, by decide, canonicalPose7_1002, canonicalMatch7_1002, indexedKeyDecode7_1002⟩
  · exact ⟨⟨877, by decide⟩, IndexedData7.key1003, by decide, canonicalPose7_1003, canonicalMatch7_1003, indexedKeyDecode7_1003⟩
  · exact ⟨⟨878, by decide⟩, IndexedData7.key1004, by decide, canonicalPose7_1004, canonicalMatch7_1004, indexedKeyDecode7_1004⟩
  · exact ⟨⟨879, by decide⟩, IndexedData7.key1005, by decide, canonicalPose7_1005, canonicalMatch7_1005, indexedKeyDecode7_1005⟩
  · exact ⟨⟨880, by decide⟩, IndexedData7.key1006, by decide, canonicalPose7_1006, canonicalMatch7_1006, indexedKeyDecode7_1006⟩
  · exact ⟨⟨881, by decide⟩, IndexedData7.key1007, by decide, canonicalPose7_1007, canonicalMatch7_1007, indexedKeyDecode7_1007⟩
  · exact ⟨⟨882, by decide⟩, IndexedData7.key1008, by decide, canonicalPose7_1008, canonicalMatch7_1008, indexedKeyDecode7_1008⟩
  · exact ⟨⟨883, by decide⟩, IndexedData7.key1009, by decide, canonicalPose7_1009, canonicalMatch7_1009, indexedKeyDecode7_1009⟩
  · exact ⟨⟨884, by decide⟩, IndexedData7.key1010, by decide, canonicalPose7_1010, canonicalMatch7_1010, indexedKeyDecode7_1010⟩
  · exact ⟨⟨885, by decide⟩, IndexedData7.key1011, by decide, canonicalPose7_1011, canonicalMatch7_1011, indexedKeyDecode7_1011⟩
  · exact ⟨⟨885, by decide⟩, IndexedData7.key1012, by decide, canonicalPose7_1012, canonicalMatch7_1012, indexedKeyDecode7_1012⟩
  · exact ⟨⟨886, by decide⟩, IndexedData7.key1013, by decide, canonicalPose7_1013, canonicalMatch7_1013, indexedKeyDecode7_1013⟩
  · exact ⟨⟨887, by decide⟩, IndexedData7.key1014, by decide, canonicalPose7_1014, canonicalMatch7_1014, indexedKeyDecode7_1014⟩
  · exact ⟨⟨888, by decide⟩, IndexedData7.key1015, by decide, canonicalPose7_1015, canonicalMatch7_1015, indexedKeyDecode7_1015⟩
  · exact ⟨⟨889, by decide⟩, IndexedData7.key1016, by decide, canonicalPose7_1016, canonicalMatch7_1016, indexedKeyDecode7_1016⟩
  · exact ⟨⟨890, by decide⟩, IndexedData7.key1017, by decide, canonicalPose7_1017, canonicalMatch7_1017, indexedKeyDecode7_1017⟩
  · exact ⟨⟨891, by decide⟩, IndexedData7.key1018, by decide, canonicalPose7_1018, canonicalMatch7_1018, indexedKeyDecode7_1018⟩
  · exact ⟨⟨892, by decide⟩, IndexedData7.key1019, by decide, canonicalPose7_1019, canonicalMatch7_1019, indexedKeyDecode7_1019⟩
  · exact ⟨⟨893, by decide⟩, IndexedData7.key1020, by decide, canonicalPose7_1020, canonicalMatch7_1020, indexedKeyDecode7_1020⟩
  · exact ⟨⟨894, by decide⟩, IndexedData7.key1021, by decide, canonicalPose7_1021, canonicalMatch7_1021, indexedKeyDecode7_1021⟩
  · exact ⟨⟨894, by decide⟩, IndexedData7.key1022, by decide, canonicalPose7_1022, canonicalMatch7_1022, indexedKeyDecode7_1022⟩
  · exact ⟨⟨895, by decide⟩, IndexedData7.key1023, by decide, canonicalPose7_1023, canonicalMatch7_1023, indexedKeyDecode7_1023⟩

#print axioms keys7Chunk31_aligned

end SparseMonotiles.Canonical
