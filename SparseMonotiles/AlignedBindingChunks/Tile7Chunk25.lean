module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk25

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk25_aligned : ∀ k ∈ keys7Chunk25,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk25, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨699, by decide⟩, IndexedData7.key800, by decide, canonicalPose7_800, canonicalMatch7_800, indexedKeyDecode7_800⟩
  · exact ⟨⟨700, by decide⟩, IndexedData7.key801, by decide, canonicalPose7_801, canonicalMatch7_801, indexedKeyDecode7_801⟩
  · exact ⟨⟨701, by decide⟩, IndexedData7.key802, by decide, canonicalPose7_802, canonicalMatch7_802, indexedKeyDecode7_802⟩
  · exact ⟨⟨702, by decide⟩, IndexedData7.key803, by decide, canonicalPose7_803, canonicalMatch7_803, indexedKeyDecode7_803⟩
  · exact ⟨⟨703, by decide⟩, IndexedData7.key804, by decide, canonicalPose7_804, canonicalMatch7_804, indexedKeyDecode7_804⟩
  · exact ⟨⟨704, by decide⟩, IndexedData7.key805, by decide, canonicalPose7_805, canonicalMatch7_805, indexedKeyDecode7_805⟩
  · exact ⟨⟨705, by decide⟩, IndexedData7.key806, by decide, canonicalPose7_806, canonicalMatch7_806, indexedKeyDecode7_806⟩
  · exact ⟨⟨706, by decide⟩, IndexedData7.key807, by decide, canonicalPose7_807, canonicalMatch7_807, indexedKeyDecode7_807⟩
  · exact ⟨⟨706, by decide⟩, IndexedData7.key808, by decide, canonicalPose7_808, canonicalMatch7_808, indexedKeyDecode7_808⟩
  · exact ⟨⟨707, by decide⟩, IndexedData7.key809, by decide, canonicalPose7_809, canonicalMatch7_809, indexedKeyDecode7_809⟩
  · exact ⟨⟨708, by decide⟩, IndexedData7.key810, by decide, canonicalPose7_810, canonicalMatch7_810, indexedKeyDecode7_810⟩
  · exact ⟨⟨709, by decide⟩, IndexedData7.key811, by decide, canonicalPose7_811, canonicalMatch7_811, indexedKeyDecode7_811⟩
  · exact ⟨⟨710, by decide⟩, IndexedData7.key812, by decide, canonicalPose7_812, canonicalMatch7_812, indexedKeyDecode7_812⟩
  · exact ⟨⟨710, by decide⟩, IndexedData7.key813, by decide, canonicalPose7_813, canonicalMatch7_813, indexedKeyDecode7_813⟩
  · exact ⟨⟨711, by decide⟩, IndexedData7.key814, by decide, canonicalPose7_814, canonicalMatch7_814, indexedKeyDecode7_814⟩
  · exact ⟨⟨712, by decide⟩, IndexedData7.key815, by decide, canonicalPose7_815, canonicalMatch7_815, indexedKeyDecode7_815⟩
  · exact ⟨⟨713, by decide⟩, IndexedData7.key816, by decide, canonicalPose7_816, canonicalMatch7_816, indexedKeyDecode7_816⟩
  · exact ⟨⟨714, by decide⟩, IndexedData7.key817, by decide, canonicalPose7_817, canonicalMatch7_817, indexedKeyDecode7_817⟩
  · exact ⟨⟨715, by decide⟩, IndexedData7.key818, by decide, canonicalPose7_818, canonicalMatch7_818, indexedKeyDecode7_818⟩
  · exact ⟨⟨716, by decide⟩, IndexedData7.key819, by decide, canonicalPose7_819, canonicalMatch7_819, indexedKeyDecode7_819⟩
  · exact ⟨⟨717, by decide⟩, IndexedData7.key820, by decide, canonicalPose7_820, canonicalMatch7_820, indexedKeyDecode7_820⟩
  · exact ⟨⟨718, by decide⟩, IndexedData7.key821, by decide, canonicalPose7_821, canonicalMatch7_821, indexedKeyDecode7_821⟩
  · exact ⟨⟨719, by decide⟩, IndexedData7.key822, by decide, canonicalPose7_822, canonicalMatch7_822, indexedKeyDecode7_822⟩
  · exact ⟨⟨720, by decide⟩, IndexedData7.key823, by decide, canonicalPose7_823, canonicalMatch7_823, indexedKeyDecode7_823⟩
  · exact ⟨⟨721, by decide⟩, IndexedData7.key824, by decide, canonicalPose7_824, canonicalMatch7_824, indexedKeyDecode7_824⟩
  · exact ⟨⟨722, by decide⟩, IndexedData7.key825, by decide, canonicalPose7_825, canonicalMatch7_825, indexedKeyDecode7_825⟩
  · exact ⟨⟨722, by decide⟩, IndexedData7.key826, by decide, canonicalPose7_826, canonicalMatch7_826, indexedKeyDecode7_826⟩
  · exact ⟨⟨723, by decide⟩, IndexedData7.key827, by decide, canonicalPose7_827, canonicalMatch7_827, indexedKeyDecode7_827⟩
  · exact ⟨⟨724, by decide⟩, IndexedData7.key828, by decide, canonicalPose7_828, canonicalMatch7_828, indexedKeyDecode7_828⟩
  · exact ⟨⟨725, by decide⟩, IndexedData7.key829, by decide, canonicalPose7_829, canonicalMatch7_829, indexedKeyDecode7_829⟩
  · exact ⟨⟨726, by decide⟩, IndexedData7.key830, by decide, canonicalPose7_830, canonicalMatch7_830, indexedKeyDecode7_830⟩
  · exact ⟨⟨727, by decide⟩, IndexedData7.key831, by decide, canonicalPose7_831, canonicalMatch7_831, indexedKeyDecode7_831⟩

#print axioms keys7Chunk25_aligned

end SparseMonotiles.Canonical
