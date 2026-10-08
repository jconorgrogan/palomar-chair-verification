module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk30

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk30_aligned : ∀ k ∈ keys7Chunk30,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk30, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨839, by decide⟩, IndexedData7.key960, by decide, canonicalPose7_960, canonicalMatch7_960, indexedKeyDecode7_960⟩
  · exact ⟨⟨840, by decide⟩, IndexedData7.key961, by decide, canonicalPose7_961, canonicalMatch7_961, indexedKeyDecode7_961⟩
  · exact ⟨⟨841, by decide⟩, IndexedData7.key962, by decide, canonicalPose7_962, canonicalMatch7_962, indexedKeyDecode7_962⟩
  · exact ⟨⟨842, by decide⟩, IndexedData7.key963, by decide, canonicalPose7_963, canonicalMatch7_963, indexedKeyDecode7_963⟩
  · exact ⟨⟨843, by decide⟩, IndexedData7.key964, by decide, canonicalPose7_964, canonicalMatch7_964, indexedKeyDecode7_964⟩
  · exact ⟨⟨844, by decide⟩, IndexedData7.key965, by decide, canonicalPose7_965, canonicalMatch7_965, indexedKeyDecode7_965⟩
  · exact ⟨⟨845, by decide⟩, IndexedData7.key966, by decide, canonicalPose7_966, canonicalMatch7_966, indexedKeyDecode7_966⟩
  · exact ⟨⟨846, by decide⟩, IndexedData7.key967, by decide, canonicalPose7_967, canonicalMatch7_967, indexedKeyDecode7_967⟩
  · exact ⟨⟨847, by decide⟩, IndexedData7.key968, by decide, canonicalPose7_968, canonicalMatch7_968, indexedKeyDecode7_968⟩
  · exact ⟨⟨848, by decide⟩, IndexedData7.key969, by decide, canonicalPose7_969, canonicalMatch7_969, indexedKeyDecode7_969⟩
  · exact ⟨⟨849, by decide⟩, IndexedData7.key970, by decide, canonicalPose7_970, canonicalMatch7_970, indexedKeyDecode7_970⟩
  · exact ⟨⟨849, by decide⟩, IndexedData7.key971, by decide, canonicalPose7_971, canonicalMatch7_971, indexedKeyDecode7_971⟩
  · exact ⟨⟨850, by decide⟩, IndexedData7.key972, by decide, canonicalPose7_972, canonicalMatch7_972, indexedKeyDecode7_972⟩
  · exact ⟨⟨851, by decide⟩, IndexedData7.key973, by decide, canonicalPose7_973, canonicalMatch7_973, indexedKeyDecode7_973⟩
  · exact ⟨⟨852, by decide⟩, IndexedData7.key974, by decide, canonicalPose7_974, canonicalMatch7_974, indexedKeyDecode7_974⟩
  · exact ⟨⟨852, by decide⟩, IndexedData7.key975, by decide, canonicalPose7_975, canonicalMatch7_975, indexedKeyDecode7_975⟩
  · exact ⟨⟨853, by decide⟩, IndexedData7.key976, by decide, canonicalPose7_976, canonicalMatch7_976, indexedKeyDecode7_976⟩
  · exact ⟨⟨854, by decide⟩, IndexedData7.key977, by decide, canonicalPose7_977, canonicalMatch7_977, indexedKeyDecode7_977⟩
  · exact ⟨⟨855, by decide⟩, IndexedData7.key978, by decide, canonicalPose7_978, canonicalMatch7_978, indexedKeyDecode7_978⟩
  · exact ⟨⟨856, by decide⟩, IndexedData7.key979, by decide, canonicalPose7_979, canonicalMatch7_979, indexedKeyDecode7_979⟩
  · exact ⟨⟨857, by decide⟩, IndexedData7.key980, by decide, canonicalPose7_980, canonicalMatch7_980, indexedKeyDecode7_980⟩
  · exact ⟨⟨858, by decide⟩, IndexedData7.key981, by decide, canonicalPose7_981, canonicalMatch7_981, indexedKeyDecode7_981⟩
  · exact ⟨⟨859, by decide⟩, IndexedData7.key982, by decide, canonicalPose7_982, canonicalMatch7_982, indexedKeyDecode7_982⟩
  · exact ⟨⟨860, by decide⟩, IndexedData7.key983, by decide, canonicalPose7_983, canonicalMatch7_983, indexedKeyDecode7_983⟩
  · exact ⟨⟨861, by decide⟩, IndexedData7.key984, by decide, canonicalPose7_984, canonicalMatch7_984, indexedKeyDecode7_984⟩
  · exact ⟨⟨862, by decide⟩, IndexedData7.key985, by decide, canonicalPose7_985, canonicalMatch7_985, indexedKeyDecode7_985⟩
  · exact ⟨⟨863, by decide⟩, IndexedData7.key986, by decide, canonicalPose7_986, canonicalMatch7_986, indexedKeyDecode7_986⟩
  · exact ⟨⟨863, by decide⟩, IndexedData7.key987, by decide, canonicalPose7_987, canonicalMatch7_987, indexedKeyDecode7_987⟩
  · exact ⟨⟨864, by decide⟩, IndexedData7.key988, by decide, canonicalPose7_988, canonicalMatch7_988, indexedKeyDecode7_988⟩
  · exact ⟨⟨865, by decide⟩, IndexedData7.key989, by decide, canonicalPose7_989, canonicalMatch7_989, indexedKeyDecode7_989⟩
  · exact ⟨⟨866, by decide⟩, IndexedData7.key990, by decide, canonicalPose7_990, canonicalMatch7_990, indexedKeyDecode7_990⟩
  · exact ⟨⟨867, by decide⟩, IndexedData7.key991, by decide, canonicalPose7_991, canonicalMatch7_991, indexedKeyDecode7_991⟩

#print axioms keys7Chunk30_aligned

end SparseMonotiles.Canonical
