module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk19

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk19_aligned : ∀ k ∈ keys7Chunk19,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk19, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨531, by decide⟩, IndexedData7.key608, by decide, canonicalPose7_608, canonicalMatch7_608, indexedKeyDecode7_608⟩
  · exact ⟨⟨532, by decide⟩, IndexedData7.key609, by decide, canonicalPose7_609, canonicalMatch7_609, indexedKeyDecode7_609⟩
  · exact ⟨⟨533, by decide⟩, IndexedData7.key610, by decide, canonicalPose7_610, canonicalMatch7_610, indexedKeyDecode7_610⟩
  · exact ⟨⟨533, by decide⟩, IndexedData7.key611, by decide, canonicalPose7_611, canonicalMatch7_611, indexedKeyDecode7_611⟩
  · exact ⟨⟨534, by decide⟩, IndexedData7.key612, by decide, canonicalPose7_612, canonicalMatch7_612, indexedKeyDecode7_612⟩
  · exact ⟨⟨535, by decide⟩, IndexedData7.key613, by decide, canonicalPose7_613, canonicalMatch7_613, indexedKeyDecode7_613⟩
  · exact ⟨⟨536, by decide⟩, IndexedData7.key614, by decide, canonicalPose7_614, canonicalMatch7_614, indexedKeyDecode7_614⟩
  · exact ⟨⟨537, by decide⟩, IndexedData7.key615, by decide, canonicalPose7_615, canonicalMatch7_615, indexedKeyDecode7_615⟩
  · exact ⟨⟨538, by decide⟩, IndexedData7.key616, by decide, canonicalPose7_616, canonicalMatch7_616, indexedKeyDecode7_616⟩
  · exact ⟨⟨539, by decide⟩, IndexedData7.key617, by decide, canonicalPose7_617, canonicalMatch7_617, indexedKeyDecode7_617⟩
  · exact ⟨⟨540, by decide⟩, IndexedData7.key618, by decide, canonicalPose7_618, canonicalMatch7_618, indexedKeyDecode7_618⟩
  · exact ⟨⟨541, by decide⟩, IndexedData7.key619, by decide, canonicalPose7_619, canonicalMatch7_619, indexedKeyDecode7_619⟩
  · exact ⟨⟨542, by decide⟩, IndexedData7.key620, by decide, canonicalPose7_620, canonicalMatch7_620, indexedKeyDecode7_620⟩
  · exact ⟨⟨543, by decide⟩, IndexedData7.key621, by decide, canonicalPose7_621, canonicalMatch7_621, indexedKeyDecode7_621⟩
  · exact ⟨⟨544, by decide⟩, IndexedData7.key622, by decide, canonicalPose7_622, canonicalMatch7_622, indexedKeyDecode7_622⟩
  · exact ⟨⟨545, by decide⟩, IndexedData7.key623, by decide, canonicalPose7_623, canonicalMatch7_623, indexedKeyDecode7_623⟩
  · exact ⟨⟨545, by decide⟩, IndexedData7.key624, by decide, canonicalPose7_624, canonicalMatch7_624, indexedKeyDecode7_624⟩
  · exact ⟨⟨546, by decide⟩, IndexedData7.key625, by decide, canonicalPose7_625, canonicalMatch7_625, indexedKeyDecode7_625⟩
  · exact ⟨⟨547, by decide⟩, IndexedData7.key626, by decide, canonicalPose7_626, canonicalMatch7_626, indexedKeyDecode7_626⟩
  · exact ⟨⟨548, by decide⟩, IndexedData7.key627, by decide, canonicalPose7_627, canonicalMatch7_627, indexedKeyDecode7_627⟩
  · exact ⟨⟨549, by decide⟩, IndexedData7.key628, by decide, canonicalPose7_628, canonicalMatch7_628, indexedKeyDecode7_628⟩
  · exact ⟨⟨550, by decide⟩, IndexedData7.key629, by decide, canonicalPose7_629, canonicalMatch7_629, indexedKeyDecode7_629⟩
  · exact ⟨⟨550, by decide⟩, IndexedData7.key630, by decide, canonicalPose7_630, canonicalMatch7_630, indexedKeyDecode7_630⟩
  · exact ⟨⟨551, by decide⟩, IndexedData7.key631, by decide, canonicalPose7_631, canonicalMatch7_631, indexedKeyDecode7_631⟩
  · exact ⟨⟨552, by decide⟩, IndexedData7.key632, by decide, canonicalPose7_632, canonicalMatch7_632, indexedKeyDecode7_632⟩
  · exact ⟨⟨553, by decide⟩, IndexedData7.key633, by decide, canonicalPose7_633, canonicalMatch7_633, indexedKeyDecode7_633⟩
  · exact ⟨⟨554, by decide⟩, IndexedData7.key634, by decide, canonicalPose7_634, canonicalMatch7_634, indexedKeyDecode7_634⟩
  · exact ⟨⟨555, by decide⟩, IndexedData7.key635, by decide, canonicalPose7_635, canonicalMatch7_635, indexedKeyDecode7_635⟩
  · exact ⟨⟨556, by decide⟩, IndexedData7.key636, by decide, canonicalPose7_636, canonicalMatch7_636, indexedKeyDecode7_636⟩
  · exact ⟨⟨557, by decide⟩, IndexedData7.key637, by decide, canonicalPose7_637, canonicalMatch7_637, indexedKeyDecode7_637⟩
  · exact ⟨⟨558, by decide⟩, IndexedData7.key638, by decide, canonicalPose7_638, canonicalMatch7_638, indexedKeyDecode7_638⟩
  · exact ⟨⟨559, by decide⟩, IndexedData7.key639, by decide, canonicalPose7_639, canonicalMatch7_639, indexedKeyDecode7_639⟩

#print axioms keys7Chunk19_aligned

end SparseMonotiles.Canonical
