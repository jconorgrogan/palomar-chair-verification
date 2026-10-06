module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk18

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk18_aligned : ∀ k ∈ keys7Chunk18,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk18, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨503, by decide⟩, IndexedData7.key576, by decide, canonicalPose7_576, canonicalMatch7_576, indexedKeyDecode7_576⟩
  · exact ⟨⟨504, by decide⟩, IndexedData7.key577, by decide, canonicalPose7_577, canonicalMatch7_577, indexedKeyDecode7_577⟩
  · exact ⟨⟨505, by decide⟩, IndexedData7.key578, by decide, canonicalPose7_578, canonicalMatch7_578, indexedKeyDecode7_578⟩
  · exact ⟨⟨506, by decide⟩, IndexedData7.key579, by decide, canonicalPose7_579, canonicalMatch7_579, indexedKeyDecode7_579⟩
  · exact ⟨⟨507, by decide⟩, IndexedData7.key580, by decide, canonicalPose7_580, canonicalMatch7_580, indexedKeyDecode7_580⟩
  · exact ⟨⟨508, by decide⟩, IndexedData7.key581, by decide, canonicalPose7_581, canonicalMatch7_581, indexedKeyDecode7_581⟩
  · exact ⟨⟨509, by decide⟩, IndexedData7.key582, by decide, canonicalPose7_582, canonicalMatch7_582, indexedKeyDecode7_582⟩
  · exact ⟨⟨510, by decide⟩, IndexedData7.key583, by decide, canonicalPose7_583, canonicalMatch7_583, indexedKeyDecode7_583⟩
  · exact ⟨⟨510, by decide⟩, IndexedData7.key584, by decide, canonicalPose7_584, canonicalMatch7_584, indexedKeyDecode7_584⟩
  · exact ⟨⟨511, by decide⟩, IndexedData7.key585, by decide, canonicalPose7_585, canonicalMatch7_585, indexedKeyDecode7_585⟩
  · exact ⟨⟨512, by decide⟩, IndexedData7.key586, by decide, canonicalPose7_586, canonicalMatch7_586, indexedKeyDecode7_586⟩
  · exact ⟨⟨513, by decide⟩, IndexedData7.key587, by decide, canonicalPose7_587, canonicalMatch7_587, indexedKeyDecode7_587⟩
  · exact ⟨⟨514, by decide⟩, IndexedData7.key588, by decide, canonicalPose7_588, canonicalMatch7_588, indexedKeyDecode7_588⟩
  · exact ⟨⟨515, by decide⟩, IndexedData7.key589, by decide, canonicalPose7_589, canonicalMatch7_589, indexedKeyDecode7_589⟩
  · exact ⟨⟨515, by decide⟩, IndexedData7.key590, by decide, canonicalPose7_590, canonicalMatch7_590, indexedKeyDecode7_590⟩
  · exact ⟨⟨516, by decide⟩, IndexedData7.key591, by decide, canonicalPose7_591, canonicalMatch7_591, indexedKeyDecode7_591⟩
  · exact ⟨⟨517, by decide⟩, IndexedData7.key592, by decide, canonicalPose7_592, canonicalMatch7_592, indexedKeyDecode7_592⟩
  · exact ⟨⟨518, by decide⟩, IndexedData7.key593, by decide, canonicalPose7_593, canonicalMatch7_593, indexedKeyDecode7_593⟩
  · exact ⟨⟨519, by decide⟩, IndexedData7.key594, by decide, canonicalPose7_594, canonicalMatch7_594, indexedKeyDecode7_594⟩
  · exact ⟨⟨520, by decide⟩, IndexedData7.key595, by decide, canonicalPose7_595, canonicalMatch7_595, indexedKeyDecode7_595⟩
  · exact ⟨⟨521, by decide⟩, IndexedData7.key596, by decide, canonicalPose7_596, canonicalMatch7_596, indexedKeyDecode7_596⟩
  · exact ⟨⟨522, by decide⟩, IndexedData7.key597, by decide, canonicalPose7_597, canonicalMatch7_597, indexedKeyDecode7_597⟩
  · exact ⟨⟨523, by decide⟩, IndexedData7.key598, by decide, canonicalPose7_598, canonicalMatch7_598, indexedKeyDecode7_598⟩
  · exact ⟨⟨524, by decide⟩, IndexedData7.key599, by decide, canonicalPose7_599, canonicalMatch7_599, indexedKeyDecode7_599⟩
  · exact ⟨⟨524, by decide⟩, IndexedData7.key600, by decide, canonicalPose7_600, canonicalMatch7_600, indexedKeyDecode7_600⟩
  · exact ⟨⟨525, by decide⟩, IndexedData7.key601, by decide, canonicalPose7_601, canonicalMatch7_601, indexedKeyDecode7_601⟩
  · exact ⟨⟨526, by decide⟩, IndexedData7.key602, by decide, canonicalPose7_602, canonicalMatch7_602, indexedKeyDecode7_602⟩
  · exact ⟨⟨526, by decide⟩, IndexedData7.key603, by decide, canonicalPose7_603, canonicalMatch7_603, indexedKeyDecode7_603⟩
  · exact ⟨⟨527, by decide⟩, IndexedData7.key604, by decide, canonicalPose7_604, canonicalMatch7_604, indexedKeyDecode7_604⟩
  · exact ⟨⟨528, by decide⟩, IndexedData7.key605, by decide, canonicalPose7_605, canonicalMatch7_605, indexedKeyDecode7_605⟩
  · exact ⟨⟨529, by decide⟩, IndexedData7.key606, by decide, canonicalPose7_606, canonicalMatch7_606, indexedKeyDecode7_606⟩
  · exact ⟨⟨530, by decide⟩, IndexedData7.key607, by decide, canonicalPose7_607, canonicalMatch7_607, indexedKeyDecode7_607⟩

#print axioms keys7Chunk18_aligned

end SparseMonotiles.Canonical
