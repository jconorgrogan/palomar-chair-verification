module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk27

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk27_aligned : ∀ k ∈ keys7Chunk27,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk27, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨755, by decide⟩, IndexedData7.key864, by decide, canonicalPose7_864, canonicalMatch7_864, indexedKeyDecode7_864⟩
  · exact ⟨⟨756, by decide⟩, IndexedData7.key865, by decide, canonicalPose7_865, canonicalMatch7_865, indexedKeyDecode7_865⟩
  · exact ⟨⟨757, by decide⟩, IndexedData7.key866, by decide, canonicalPose7_866, canonicalMatch7_866, indexedKeyDecode7_866⟩
  · exact ⟨⟨758, by decide⟩, IndexedData7.key867, by decide, canonicalPose7_867, canonicalMatch7_867, indexedKeyDecode7_867⟩
  · exact ⟨⟨759, by decide⟩, IndexedData7.key868, by decide, canonicalPose7_868, canonicalMatch7_868, indexedKeyDecode7_868⟩
  · exact ⟨⟨760, by decide⟩, IndexedData7.key869, by decide, canonicalPose7_869, canonicalMatch7_869, indexedKeyDecode7_869⟩
  · exact ⟨⟨760, by decide⟩, IndexedData7.key870, by decide, canonicalPose7_870, canonicalMatch7_870, indexedKeyDecode7_870⟩
  · exact ⟨⟨761, by decide⟩, IndexedData7.key871, by decide, canonicalPose7_871, canonicalMatch7_871, indexedKeyDecode7_871⟩
  · exact ⟨⟨762, by decide⟩, IndexedData7.key872, by decide, canonicalPose7_872, canonicalMatch7_872, indexedKeyDecode7_872⟩
  · exact ⟨⟨763, by decide⟩, IndexedData7.key873, by decide, canonicalPose7_873, canonicalMatch7_873, indexedKeyDecode7_873⟩
  · exact ⟨⟨764, by decide⟩, IndexedData7.key874, by decide, canonicalPose7_874, canonicalMatch7_874, indexedKeyDecode7_874⟩
  · exact ⟨⟨765, by decide⟩, IndexedData7.key875, by decide, canonicalPose7_875, canonicalMatch7_875, indexedKeyDecode7_875⟩
  · exact ⟨⟨765, by decide⟩, IndexedData7.key876, by decide, canonicalPose7_876, canonicalMatch7_876, indexedKeyDecode7_876⟩
  · exact ⟨⟨766, by decide⟩, IndexedData7.key877, by decide, canonicalPose7_877, canonicalMatch7_877, indexedKeyDecode7_877⟩
  · exact ⟨⟨767, by decide⟩, IndexedData7.key878, by decide, canonicalPose7_878, canonicalMatch7_878, indexedKeyDecode7_878⟩
  · exact ⟨⟨768, by decide⟩, IndexedData7.key879, by decide, canonicalPose7_879, canonicalMatch7_879, indexedKeyDecode7_879⟩
  · exact ⟨⟨769, by decide⟩, IndexedData7.key880, by decide, canonicalPose7_880, canonicalMatch7_880, indexedKeyDecode7_880⟩
  · exact ⟨⟨770, by decide⟩, IndexedData7.key881, by decide, canonicalPose7_881, canonicalMatch7_881, indexedKeyDecode7_881⟩
  · exact ⟨⟨771, by decide⟩, IndexedData7.key882, by decide, canonicalPose7_882, canonicalMatch7_882, indexedKeyDecode7_882⟩
  · exact ⟨⟨772, by decide⟩, IndexedData7.key883, by decide, canonicalPose7_883, canonicalMatch7_883, indexedKeyDecode7_883⟩
  · exact ⟨⟨773, by decide⟩, IndexedData7.key884, by decide, canonicalPose7_884, canonicalMatch7_884, indexedKeyDecode7_884⟩
  · exact ⟨⟨774, by decide⟩, IndexedData7.key885, by decide, canonicalPose7_885, canonicalMatch7_885, indexedKeyDecode7_885⟩
  · exact ⟨⟨775, by decide⟩, IndexedData7.key886, by decide, canonicalPose7_886, canonicalMatch7_886, indexedKeyDecode7_886⟩
  · exact ⟨⟨776, by decide⟩, IndexedData7.key887, by decide, canonicalPose7_887, canonicalMatch7_887, indexedKeyDecode7_887⟩
  · exact ⟨⟨776, by decide⟩, IndexedData7.key888, by decide, canonicalPose7_888, canonicalMatch7_888, indexedKeyDecode7_888⟩
  · exact ⟨⟨777, by decide⟩, IndexedData7.key889, by decide, canonicalPose7_889, canonicalMatch7_889, indexedKeyDecode7_889⟩
  · exact ⟨⟨778, by decide⟩, IndexedData7.key890, by decide, canonicalPose7_890, canonicalMatch7_890, indexedKeyDecode7_890⟩
  · exact ⟨⟨779, by decide⟩, IndexedData7.key891, by decide, canonicalPose7_891, canonicalMatch7_891, indexedKeyDecode7_891⟩
  · exact ⟨⟨780, by decide⟩, IndexedData7.key892, by decide, canonicalPose7_892, canonicalMatch7_892, indexedKeyDecode7_892⟩
  · exact ⟨⟨781, by decide⟩, IndexedData7.key893, by decide, canonicalPose7_893, canonicalMatch7_893, indexedKeyDecode7_893⟩
  · exact ⟨⟨781, by decide⟩, IndexedData7.key894, by decide, canonicalPose7_894, canonicalMatch7_894, indexedKeyDecode7_894⟩
  · exact ⟨⟨782, by decide⟩, IndexedData7.key895, by decide, canonicalPose7_895, canonicalMatch7_895, indexedKeyDecode7_895⟩

#print axioms keys7Chunk27_aligned

end SparseMonotiles.Canonical
