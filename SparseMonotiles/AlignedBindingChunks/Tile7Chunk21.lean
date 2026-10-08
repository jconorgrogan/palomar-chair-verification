module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk21

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk21_aligned : ∀ k ∈ keys7Chunk21,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk21, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨587, by decide⟩, IndexedData7.key672, by decide, canonicalPose7_672, canonicalMatch7_672, indexedKeyDecode7_672⟩
  · exact ⟨⟨588, by decide⟩, IndexedData7.key673, by decide, canonicalPose7_673, canonicalMatch7_673, indexedKeyDecode7_673⟩
  · exact ⟨⟨589, by decide⟩, IndexedData7.key674, by decide, canonicalPose7_674, canonicalMatch7_674, indexedKeyDecode7_674⟩
  · exact ⟨⟨590, by decide⟩, IndexedData7.key675, by decide, canonicalPose7_675, canonicalMatch7_675, indexedKeyDecode7_675⟩
  · exact ⟨⟨591, by decide⟩, IndexedData7.key676, by decide, canonicalPose7_676, canonicalMatch7_676, indexedKeyDecode7_676⟩
  · exact ⟨⟨591, by decide⟩, IndexedData7.key677, by decide, canonicalPose7_677, canonicalMatch7_677, indexedKeyDecode7_677⟩
  · exact ⟨⟨592, by decide⟩, IndexedData7.key678, by decide, canonicalPose7_678, canonicalMatch7_678, indexedKeyDecode7_678⟩
  · exact ⟨⟨593, by decide⟩, IndexedData7.key679, by decide, canonicalPose7_679, canonicalMatch7_679, indexedKeyDecode7_679⟩
  · exact ⟨⟨594, by decide⟩, IndexedData7.key680, by decide, canonicalPose7_680, canonicalMatch7_680, indexedKeyDecode7_680⟩
  · exact ⟨⟨595, by decide⟩, IndexedData7.key681, by decide, canonicalPose7_681, canonicalMatch7_681, indexedKeyDecode7_681⟩
  · exact ⟨⟨596, by decide⟩, IndexedData7.key682, by decide, canonicalPose7_682, canonicalMatch7_682, indexedKeyDecode7_682⟩
  · exact ⟨⟨597, by decide⟩, IndexedData7.key683, by decide, canonicalPose7_683, canonicalMatch7_683, indexedKeyDecode7_683⟩
  · exact ⟨⟨598, by decide⟩, IndexedData7.key684, by decide, canonicalPose7_684, canonicalMatch7_684, indexedKeyDecode7_684⟩
  · exact ⟨⟨599, by decide⟩, IndexedData7.key685, by decide, canonicalPose7_685, canonicalMatch7_685, indexedKeyDecode7_685⟩
  · exact ⟨⟨599, by decide⟩, IndexedData7.key686, by decide, canonicalPose7_686, canonicalMatch7_686, indexedKeyDecode7_686⟩
  · exact ⟨⟨600, by decide⟩, IndexedData7.key687, by decide, canonicalPose7_687, canonicalMatch7_687, indexedKeyDecode7_687⟩
  · exact ⟨⟨601, by decide⟩, IndexedData7.key688, by decide, canonicalPose7_688, canonicalMatch7_688, indexedKeyDecode7_688⟩
  · exact ⟨⟨602, by decide⟩, IndexedData7.key689, by decide, canonicalPose7_689, canonicalMatch7_689, indexedKeyDecode7_689⟩
  · exact ⟨⟨603, by decide⟩, IndexedData7.key690, by decide, canonicalPose7_690, canonicalMatch7_690, indexedKeyDecode7_690⟩
  · exact ⟨⟨604, by decide⟩, IndexedData7.key691, by decide, canonicalPose7_691, canonicalMatch7_691, indexedKeyDecode7_691⟩
  · exact ⟨⟨604, by decide⟩, IndexedData7.key692, by decide, canonicalPose7_692, canonicalMatch7_692, indexedKeyDecode7_692⟩
  · exact ⟨⟨605, by decide⟩, IndexedData7.key693, by decide, canonicalPose7_693, canonicalMatch7_693, indexedKeyDecode7_693⟩
  · exact ⟨⟨606, by decide⟩, IndexedData7.key694, by decide, canonicalPose7_694, canonicalMatch7_694, indexedKeyDecode7_694⟩
  · exact ⟨⟨607, by decide⟩, IndexedData7.key695, by decide, canonicalPose7_695, canonicalMatch7_695, indexedKeyDecode7_695⟩
  · exact ⟨⟨608, by decide⟩, IndexedData7.key696, by decide, canonicalPose7_696, canonicalMatch7_696, indexedKeyDecode7_696⟩
  · exact ⟨⟨609, by decide⟩, IndexedData7.key697, by decide, canonicalPose7_697, canonicalMatch7_697, indexedKeyDecode7_697⟩
  · exact ⟨⟨610, by decide⟩, IndexedData7.key698, by decide, canonicalPose7_698, canonicalMatch7_698, indexedKeyDecode7_698⟩
  · exact ⟨⟨611, by decide⟩, IndexedData7.key699, by decide, canonicalPose7_699, canonicalMatch7_699, indexedKeyDecode7_699⟩
  · exact ⟨⟨612, by decide⟩, IndexedData7.key700, by decide, canonicalPose7_700, canonicalMatch7_700, indexedKeyDecode7_700⟩
  · exact ⟨⟨612, by decide⟩, IndexedData7.key701, by decide, canonicalPose7_701, canonicalMatch7_701, indexedKeyDecode7_701⟩
  · exact ⟨⟨613, by decide⟩, IndexedData7.key702, by decide, canonicalPose7_702, canonicalMatch7_702, indexedKeyDecode7_702⟩
  · exact ⟨⟨614, by decide⟩, IndexedData7.key703, by decide, canonicalPose7_703, canonicalMatch7_703, indexedKeyDecode7_703⟩

#print axioms keys7Chunk21_aligned

end SparseMonotiles.Canonical
