module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk28

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk28_aligned : ∀ k ∈ keys7Chunk28,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk28, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨783, by decide⟩, IndexedData7.key896, by decide, canonicalPose7_896, canonicalMatch7_896, indexedKeyDecode7_896⟩
  · exact ⟨⟨784, by decide⟩, IndexedData7.key897, by decide, canonicalPose7_897, canonicalMatch7_897, indexedKeyDecode7_897⟩
  · exact ⟨⟨785, by decide⟩, IndexedData7.key898, by decide, canonicalPose7_898, canonicalMatch7_898, indexedKeyDecode7_898⟩
  · exact ⟨⟨786, by decide⟩, IndexedData7.key899, by decide, canonicalPose7_899, canonicalMatch7_899, indexedKeyDecode7_899⟩
  · exact ⟨⟨787, by decide⟩, IndexedData7.key900, by decide, canonicalPose7_900, canonicalMatch7_900, indexedKeyDecode7_900⟩
  · exact ⟨⟨788, by decide⟩, IndexedData7.key901, by decide, canonicalPose7_901, canonicalMatch7_901, indexedKeyDecode7_901⟩
  · exact ⟨⟨788, by decide⟩, IndexedData7.key902, by decide, canonicalPose7_902, canonicalMatch7_902, indexedKeyDecode7_902⟩
  · exact ⟨⟨789, by decide⟩, IndexedData7.key903, by decide, canonicalPose7_903, canonicalMatch7_903, indexedKeyDecode7_903⟩
  · exact ⟨⟨790, by decide⟩, IndexedData7.key904, by decide, canonicalPose7_904, canonicalMatch7_904, indexedKeyDecode7_904⟩
  · exact ⟨⟨791, by decide⟩, IndexedData7.key905, by decide, canonicalPose7_905, canonicalMatch7_905, indexedKeyDecode7_905⟩
  · exact ⟨⟨792, by decide⟩, IndexedData7.key906, by decide, canonicalPose7_906, canonicalMatch7_906, indexedKeyDecode7_906⟩
  · exact ⟨⟨793, by decide⟩, IndexedData7.key907, by decide, canonicalPose7_907, canonicalMatch7_907, indexedKeyDecode7_907⟩
  · exact ⟨⟨794, by decide⟩, IndexedData7.key908, by decide, canonicalPose7_908, canonicalMatch7_908, indexedKeyDecode7_908⟩
  · exact ⟨⟨795, by decide⟩, IndexedData7.key909, by decide, canonicalPose7_909, canonicalMatch7_909, indexedKeyDecode7_909⟩
  · exact ⟨⟨796, by decide⟩, IndexedData7.key910, by decide, canonicalPose7_910, canonicalMatch7_910, indexedKeyDecode7_910⟩
  · exact ⟨⟨797, by decide⟩, IndexedData7.key911, by decide, canonicalPose7_911, canonicalMatch7_911, indexedKeyDecode7_911⟩
  · exact ⟨⟨798, by decide⟩, IndexedData7.key912, by decide, canonicalPose7_912, canonicalMatch7_912, indexedKeyDecode7_912⟩
  · exact ⟨⟨798, by decide⟩, IndexedData7.key913, by decide, canonicalPose7_913, canonicalMatch7_913, indexedKeyDecode7_913⟩
  · exact ⟨⟨799, by decide⟩, IndexedData7.key914, by decide, canonicalPose7_914, canonicalMatch7_914, indexedKeyDecode7_914⟩
  · exact ⟨⟨800, by decide⟩, IndexedData7.key915, by decide, canonicalPose7_915, canonicalMatch7_915, indexedKeyDecode7_915⟩
  · exact ⟨⟨801, by decide⟩, IndexedData7.key916, by decide, canonicalPose7_916, canonicalMatch7_916, indexedKeyDecode7_916⟩
  · exact ⟨⟨802, by decide⟩, IndexedData7.key917, by decide, canonicalPose7_917, canonicalMatch7_917, indexedKeyDecode7_917⟩
  · exact ⟨⟨803, by decide⟩, IndexedData7.key918, by decide, canonicalPose7_918, canonicalMatch7_918, indexedKeyDecode7_918⟩
  · exact ⟨⟨803, by decide⟩, IndexedData7.key919, by decide, canonicalPose7_919, canonicalMatch7_919, indexedKeyDecode7_919⟩
  · exact ⟨⟨804, by decide⟩, IndexedData7.key920, by decide, canonicalPose7_920, canonicalMatch7_920, indexedKeyDecode7_920⟩
  · exact ⟨⟨805, by decide⟩, IndexedData7.key921, by decide, canonicalPose7_921, canonicalMatch7_921, indexedKeyDecode7_921⟩
  · exact ⟨⟨806, by decide⟩, IndexedData7.key922, by decide, canonicalPose7_922, canonicalMatch7_922, indexedKeyDecode7_922⟩
  · exact ⟨⟨807, by decide⟩, IndexedData7.key923, by decide, canonicalPose7_923, canonicalMatch7_923, indexedKeyDecode7_923⟩
  · exact ⟨⟨808, by decide⟩, IndexedData7.key924, by decide, canonicalPose7_924, canonicalMatch7_924, indexedKeyDecode7_924⟩
  · exact ⟨⟨808, by decide⟩, IndexedData7.key925, by decide, canonicalPose7_925, canonicalMatch7_925, indexedKeyDecode7_925⟩
  · exact ⟨⟨809, by decide⟩, IndexedData7.key926, by decide, canonicalPose7_926, canonicalMatch7_926, indexedKeyDecode7_926⟩
  · exact ⟨⟨810, by decide⟩, IndexedData7.key927, by decide, canonicalPose7_927, canonicalMatch7_927, indexedKeyDecode7_927⟩

#print axioms keys7Chunk28_aligned

end SparseMonotiles.Canonical
