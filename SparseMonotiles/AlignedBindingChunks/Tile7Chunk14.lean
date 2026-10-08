module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk14

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk14_aligned : ∀ k ∈ keys7Chunk14,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk14, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨392, by decide⟩, IndexedData7.key448, by decide, canonicalPose7_448, canonicalMatch7_448, indexedKeyDecode7_448⟩
  · exact ⟨⟨393, by decide⟩, IndexedData7.key449, by decide, canonicalPose7_449, canonicalMatch7_449, indexedKeyDecode7_449⟩
  · exact ⟨⟨394, by decide⟩, IndexedData7.key450, by decide, canonicalPose7_450, canonicalMatch7_450, indexedKeyDecode7_450⟩
  · exact ⟨⟨394, by decide⟩, IndexedData7.key451, by decide, canonicalPose7_451, canonicalMatch7_451, indexedKeyDecode7_451⟩
  · exact ⟨⟨395, by decide⟩, IndexedData7.key452, by decide, canonicalPose7_452, canonicalMatch7_452, indexedKeyDecode7_452⟩
  · exact ⟨⟨396, by decide⟩, IndexedData7.key453, by decide, canonicalPose7_453, canonicalMatch7_453, indexedKeyDecode7_453⟩
  · exact ⟨⟨397, by decide⟩, IndexedData7.key454, by decide, canonicalPose7_454, canonicalMatch7_454, indexedKeyDecode7_454⟩
  · exact ⟨⟨398, by decide⟩, IndexedData7.key455, by decide, canonicalPose7_455, canonicalMatch7_455, indexedKeyDecode7_455⟩
  · exact ⟨⟨399, by decide⟩, IndexedData7.key456, by decide, canonicalPose7_456, canonicalMatch7_456, indexedKeyDecode7_456⟩
  · exact ⟨⟨400, by decide⟩, IndexedData7.key457, by decide, canonicalPose7_457, canonicalMatch7_457, indexedKeyDecode7_457⟩
  · exact ⟨⟨401, by decide⟩, IndexedData7.key458, by decide, canonicalPose7_458, canonicalMatch7_458, indexedKeyDecode7_458⟩
  · exact ⟨⟨402, by decide⟩, IndexedData7.key459, by decide, canonicalPose7_459, canonicalMatch7_459, indexedKeyDecode7_459⟩
  · exact ⟨⟨402, by decide⟩, IndexedData7.key460, by decide, canonicalPose7_460, canonicalMatch7_460, indexedKeyDecode7_460⟩
  · exact ⟨⟨403, by decide⟩, IndexedData7.key461, by decide, canonicalPose7_461, canonicalMatch7_461, indexedKeyDecode7_461⟩
  · exact ⟨⟨404, by decide⟩, IndexedData7.key462, by decide, canonicalPose7_462, canonicalMatch7_462, indexedKeyDecode7_462⟩
  · exact ⟨⟨405, by decide⟩, IndexedData7.key463, by decide, canonicalPose7_463, canonicalMatch7_463, indexedKeyDecode7_463⟩
  · exact ⟨⟨406, by decide⟩, IndexedData7.key464, by decide, canonicalPose7_464, canonicalMatch7_464, indexedKeyDecode7_464⟩
  · exact ⟨⟨407, by decide⟩, IndexedData7.key465, by decide, canonicalPose7_465, canonicalMatch7_465, indexedKeyDecode7_465⟩
  · exact ⟨⟨407, by decide⟩, IndexedData7.key466, by decide, canonicalPose7_466, canonicalMatch7_466, indexedKeyDecode7_466⟩
  · exact ⟨⟨408, by decide⟩, IndexedData7.key467, by decide, canonicalPose7_467, canonicalMatch7_467, indexedKeyDecode7_467⟩
  · exact ⟨⟨409, by decide⟩, IndexedData7.key468, by decide, canonicalPose7_468, canonicalMatch7_468, indexedKeyDecode7_468⟩
  · exact ⟨⟨410, by decide⟩, IndexedData7.key469, by decide, canonicalPose7_469, canonicalMatch7_469, indexedKeyDecode7_469⟩
  · exact ⟨⟨411, by decide⟩, IndexedData7.key470, by decide, canonicalPose7_470, canonicalMatch7_470, indexedKeyDecode7_470⟩
  · exact ⟨⟨412, by decide⟩, IndexedData7.key471, by decide, canonicalPose7_471, canonicalMatch7_471, indexedKeyDecode7_471⟩
  · exact ⟨⟨413, by decide⟩, IndexedData7.key472, by decide, canonicalPose7_472, canonicalMatch7_472, indexedKeyDecode7_472⟩
  · exact ⟨⟨414, by decide⟩, IndexedData7.key473, by decide, canonicalPose7_473, canonicalMatch7_473, indexedKeyDecode7_473⟩
  · exact ⟨⟨415, by decide⟩, IndexedData7.key474, by decide, canonicalPose7_474, canonicalMatch7_474, indexedKeyDecode7_474⟩
  · exact ⟨⟨415, by decide⟩, IndexedData7.key475, by decide, canonicalPose7_475, canonicalMatch7_475, indexedKeyDecode7_475⟩
  · exact ⟨⟨416, by decide⟩, IndexedData7.key476, by decide, canonicalPose7_476, canonicalMatch7_476, indexedKeyDecode7_476⟩
  · exact ⟨⟨417, by decide⟩, IndexedData7.key477, by decide, canonicalPose7_477, canonicalMatch7_477, indexedKeyDecode7_477⟩
  · exact ⟨⟨418, by decide⟩, IndexedData7.key478, by decide, canonicalPose7_478, canonicalMatch7_478, indexedKeyDecode7_478⟩
  · exact ⟨⟨419, by decide⟩, IndexedData7.key479, by decide, canonicalPose7_479, canonicalMatch7_479, indexedKeyDecode7_479⟩

#print axioms keys7Chunk14_aligned

end SparseMonotiles.Canonical
