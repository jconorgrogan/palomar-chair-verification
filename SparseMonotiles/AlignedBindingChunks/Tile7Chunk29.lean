module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk29

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk29_aligned : ∀ k ∈ keys7Chunk29,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk29, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨811, by decide⟩, IndexedData7.key928, by decide, canonicalPose7_928, canonicalMatch7_928, indexedKeyDecode7_928⟩
  · exact ⟨⟨812, by decide⟩, IndexedData7.key929, by decide, canonicalPose7_929, canonicalMatch7_929, indexedKeyDecode7_929⟩
  · exact ⟨⟨813, by decide⟩, IndexedData7.key930, by decide, canonicalPose7_930, canonicalMatch7_930, indexedKeyDecode7_930⟩
  · exact ⟨⟨814, by decide⟩, IndexedData7.key931, by decide, canonicalPose7_931, canonicalMatch7_931, indexedKeyDecode7_931⟩
  · exact ⟨⟨815, by decide⟩, IndexedData7.key932, by decide, canonicalPose7_932, canonicalMatch7_932, indexedKeyDecode7_932⟩
  · exact ⟨⟨815, by decide⟩, IndexedData7.key933, by decide, canonicalPose7_933, canonicalMatch7_933, indexedKeyDecode7_933⟩
  · exact ⟨⟨816, by decide⟩, IndexedData7.key934, by decide, canonicalPose7_934, canonicalMatch7_934, indexedKeyDecode7_934⟩
  · exact ⟨⟨817, by decide⟩, IndexedData7.key935, by decide, canonicalPose7_935, canonicalMatch7_935, indexedKeyDecode7_935⟩
  · exact ⟨⟨818, by decide⟩, IndexedData7.key936, by decide, canonicalPose7_936, canonicalMatch7_936, indexedKeyDecode7_936⟩
  · exact ⟨⟨819, by decide⟩, IndexedData7.key937, by decide, canonicalPose7_937, canonicalMatch7_937, indexedKeyDecode7_937⟩
  · exact ⟨⟨820, by decide⟩, IndexedData7.key938, by decide, canonicalPose7_938, canonicalMatch7_938, indexedKeyDecode7_938⟩
  · exact ⟨⟨821, by decide⟩, IndexedData7.key939, by decide, canonicalPose7_939, canonicalMatch7_939, indexedKeyDecode7_939⟩
  · exact ⟨⟨822, by decide⟩, IndexedData7.key940, by decide, canonicalPose7_940, canonicalMatch7_940, indexedKeyDecode7_940⟩
  · exact ⟨⟨823, by decide⟩, IndexedData7.key941, by decide, canonicalPose7_941, canonicalMatch7_941, indexedKeyDecode7_941⟩
  · exact ⟨⟨824, by decide⟩, IndexedData7.key942, by decide, canonicalPose7_942, canonicalMatch7_942, indexedKeyDecode7_942⟩
  · exact ⟨⟨825, by decide⟩, IndexedData7.key943, by decide, canonicalPose7_943, canonicalMatch7_943, indexedKeyDecode7_943⟩
  · exact ⟨⟨826, by decide⟩, IndexedData7.key944, by decide, canonicalPose7_944, canonicalMatch7_944, indexedKeyDecode7_944⟩
  · exact ⟨⟨826, by decide⟩, IndexedData7.key945, by decide, canonicalPose7_945, canonicalMatch7_945, indexedKeyDecode7_945⟩
  · exact ⟨⟨827, by decide⟩, IndexedData7.key946, by decide, canonicalPose7_946, canonicalMatch7_946, indexedKeyDecode7_946⟩
  · exact ⟨⟨828, by decide⟩, IndexedData7.key947, by decide, canonicalPose7_947, canonicalMatch7_947, indexedKeyDecode7_947⟩
  · exact ⟨⟨829, by decide⟩, IndexedData7.key948, by decide, canonicalPose7_948, canonicalMatch7_948, indexedKeyDecode7_948⟩
  · exact ⟨⟨830, by decide⟩, IndexedData7.key949, by decide, canonicalPose7_949, canonicalMatch7_949, indexedKeyDecode7_949⟩
  · exact ⟨⟨830, by decide⟩, IndexedData7.key950, by decide, canonicalPose7_950, canonicalMatch7_950, indexedKeyDecode7_950⟩
  · exact ⟨⟨831, by decide⟩, IndexedData7.key951, by decide, canonicalPose7_951, canonicalMatch7_951, indexedKeyDecode7_951⟩
  · exact ⟨⟨832, by decide⟩, IndexedData7.key952, by decide, canonicalPose7_952, canonicalMatch7_952, indexedKeyDecode7_952⟩
  · exact ⟨⟨833, by decide⟩, IndexedData7.key953, by decide, canonicalPose7_953, canonicalMatch7_953, indexedKeyDecode7_953⟩
  · exact ⟨⟨834, by decide⟩, IndexedData7.key954, by decide, canonicalPose7_954, canonicalMatch7_954, indexedKeyDecode7_954⟩
  · exact ⟨⟨835, by decide⟩, IndexedData7.key955, by decide, canonicalPose7_955, canonicalMatch7_955, indexedKeyDecode7_955⟩
  · exact ⟨⟨836, by decide⟩, IndexedData7.key956, by decide, canonicalPose7_956, canonicalMatch7_956, indexedKeyDecode7_956⟩
  · exact ⟨⟨837, by decide⟩, IndexedData7.key957, by decide, canonicalPose7_957, canonicalMatch7_957, indexedKeyDecode7_957⟩
  · exact ⟨⟨838, by decide⟩, IndexedData7.key958, by decide, canonicalPose7_958, canonicalMatch7_958, indexedKeyDecode7_958⟩
  · exact ⟨⟨839, by decide⟩, IndexedData7.key959, by decide, canonicalPose7_959, canonicalMatch7_959, indexedKeyDecode7_959⟩

#print axioms keys7Chunk29_aligned

end SparseMonotiles.Canonical
