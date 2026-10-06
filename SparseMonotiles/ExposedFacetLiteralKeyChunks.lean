module

public import SparseMonotiles.Tile5Data
public import SparseMonotiles.Tile7Data
public import Mathlib.Tactic.Tauto

@[expose] public section

/-! Literal chunk membership embeds into the frozen complete key lists.
These are propositional append inclusions; no geometry or data is recomputed. -/
namespace SparseMonotiles.Canonical

theorem atlasWitness_keys5Chunk0_mem {k : KeyData 5} (hk : k ∈ keys5Chunk0) :
    k ∈ keys5 := by
  simp only [keys5,List.mem_append]
  tauto

theorem atlasWitness_keys5Chunk1_mem {k : KeyData 5} (hk : k ∈ keys5Chunk1) :
    k ∈ keys5 := by
  simp only [keys5,List.mem_append]
  tauto

theorem atlasWitness_keys5Chunk2_mem {k : KeyData 5} (hk : k ∈ keys5Chunk2) :
    k ∈ keys5 := by
  simp only [keys5,List.mem_append]
  tauto

theorem atlasWitness_keys5Chunk3_mem {k : KeyData 5} (hk : k ∈ keys5Chunk3) :
    k ∈ keys5 := by
  simp only [keys5,List.mem_append]
  tauto

theorem atlasWitness_keys5Chunk4_mem {k : KeyData 5} (hk : k ∈ keys5Chunk4) :
    k ∈ keys5 := by
  simp only [keys5,List.mem_append]
  tauto

theorem atlasWitness_keys5Chunk5_mem {k : KeyData 5} (hk : k ∈ keys5Chunk5) :
    k ∈ keys5 := by
  simp only [keys5,List.mem_append]
  tauto

theorem atlasWitness_keys5Chunk6_mem {k : KeyData 5} (hk : k ∈ keys5Chunk6) :
    k ∈ keys5 := by
  simp only [keys5,List.mem_append]
  tauto

theorem atlasWitness_keys5Chunk7_mem {k : KeyData 5} (hk : k ∈ keys5Chunk7) :
    k ∈ keys5 := by
  simp only [keys5,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk0_mem {k : KeyData 7} (hk : k ∈ keys7Chunk0) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk1_mem {k : KeyData 7} (hk : k ∈ keys7Chunk1) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk2_mem {k : KeyData 7} (hk : k ∈ keys7Chunk2) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk3_mem {k : KeyData 7} (hk : k ∈ keys7Chunk3) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk4_mem {k : KeyData 7} (hk : k ∈ keys7Chunk4) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk5_mem {k : KeyData 7} (hk : k ∈ keys7Chunk5) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk6_mem {k : KeyData 7} (hk : k ∈ keys7Chunk6) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk7_mem {k : KeyData 7} (hk : k ∈ keys7Chunk7) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk8_mem {k : KeyData 7} (hk : k ∈ keys7Chunk8) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk9_mem {k : KeyData 7} (hk : k ∈ keys7Chunk9) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk10_mem {k : KeyData 7} (hk : k ∈ keys7Chunk10) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk11_mem {k : KeyData 7} (hk : k ∈ keys7Chunk11) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk12_mem {k : KeyData 7} (hk : k ∈ keys7Chunk12) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk13_mem {k : KeyData 7} (hk : k ∈ keys7Chunk13) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk14_mem {k : KeyData 7} (hk : k ∈ keys7Chunk14) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk15_mem {k : KeyData 7} (hk : k ∈ keys7Chunk15) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk16_mem {k : KeyData 7} (hk : k ∈ keys7Chunk16) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk17_mem {k : KeyData 7} (hk : k ∈ keys7Chunk17) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk18_mem {k : KeyData 7} (hk : k ∈ keys7Chunk18) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk19_mem {k : KeyData 7} (hk : k ∈ keys7Chunk19) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk20_mem {k : KeyData 7} (hk : k ∈ keys7Chunk20) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk21_mem {k : KeyData 7} (hk : k ∈ keys7Chunk21) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk22_mem {k : KeyData 7} (hk : k ∈ keys7Chunk22) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk23_mem {k : KeyData 7} (hk : k ∈ keys7Chunk23) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk24_mem {k : KeyData 7} (hk : k ∈ keys7Chunk24) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk25_mem {k : KeyData 7} (hk : k ∈ keys7Chunk25) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk26_mem {k : KeyData 7} (hk : k ∈ keys7Chunk26) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk27_mem {k : KeyData 7} (hk : k ∈ keys7Chunk27) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk28_mem {k : KeyData 7} (hk : k ∈ keys7Chunk28) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk29_mem {k : KeyData 7} (hk : k ∈ keys7Chunk29) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk30_mem {k : KeyData 7} (hk : k ∈ keys7Chunk30) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

theorem atlasWitness_keys7Chunk31_mem {k : KeyData 7} (hk : k ∈ keys7Chunk31) :
    k ∈ keys7 := by
  simp only [keys7,List.mem_append]
  tauto

end SparseMonotiles.Canonical
