module

public import HENRY.Statement
public import SparseMonotiles.Tile7Data

@[expose] public section
namespace HENRY.Binding

set_option maxRecDepth 100000

def toInternal {d : ℕ} (k : PalomarMonotiles.KeyData d) : SparseMonotiles.KeyData d :=
  ⟨k.centre, k.radius, k.apex, k.bump⟩

theorem keySolid_eq {d : ℕ} (k : PalomarMonotiles.KeyData d) :
    PalomarMonotiles.keySolid k = SparseMonotiles.keySolid (toInternal k) := rfl

theorem keyUnion_eq {d : ℕ} (ks : List (PalomarMonotiles.KeyData d)) (b : Bool) :
    PalomarMonotiles.keyUnion ks b = SparseMonotiles.keyUnion (ks.map toInternal) b := by
  ext x
  simp only [PalomarMonotiles.keyUnion, SparseMonotiles.keyUnion,
    Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨k, hk, hb, hx⟩
    exact ⟨toInternal k, ⟨k, hk, rfl⟩, hb, hx⟩
  · rintro ⟨k, ⟨j, hj, rfl⟩, hb, hx⟩
    exact ⟨j, hj, hb, hx⟩

theorem body_eq {d : ℕ} (ks : List (PalomarMonotiles.KeyData d)) :
    PalomarMonotiles.body ks = SparseMonotiles.body (ks.map toInternal) := by
  unfold PalomarMonotiles.body SparseMonotiles.body
  rw [keyUnion_eq, keyUnion_eq]
  rfl

theorem keys7Chunk0_eq :
    PalomarMonotiles.keys7Chunk0.map toInternal = SparseMonotiles.keys7Chunk0 := rfl

theorem keys7Chunk1_eq :
    PalomarMonotiles.keys7Chunk1.map toInternal = SparseMonotiles.keys7Chunk1 := rfl

theorem keys7Chunk2_eq :
    PalomarMonotiles.keys7Chunk2.map toInternal = SparseMonotiles.keys7Chunk2 := rfl

theorem keys7Chunk3_eq :
    PalomarMonotiles.keys7Chunk3.map toInternal = SparseMonotiles.keys7Chunk3 := rfl

theorem keys7Chunk4_eq :
    PalomarMonotiles.keys7Chunk4.map toInternal = SparseMonotiles.keys7Chunk4 := rfl

theorem keys7Chunk5_eq :
    PalomarMonotiles.keys7Chunk5.map toInternal = SparseMonotiles.keys7Chunk5 := rfl

theorem keys7Chunk6_eq :
    PalomarMonotiles.keys7Chunk6.map toInternal = SparseMonotiles.keys7Chunk6 := rfl

theorem keys7Chunk7_eq :
    PalomarMonotiles.keys7Chunk7.map toInternal = SparseMonotiles.keys7Chunk7 := rfl

theorem keys7Chunk8_eq :
    PalomarMonotiles.keys7Chunk8.map toInternal = SparseMonotiles.keys7Chunk8 := rfl

theorem keys7Chunk9_eq :
    PalomarMonotiles.keys7Chunk9.map toInternal = SparseMonotiles.keys7Chunk9 := rfl

theorem keys7Chunk10_eq :
    PalomarMonotiles.keys7Chunk10.map toInternal = SparseMonotiles.keys7Chunk10 := rfl

theorem keys7Chunk11_eq :
    PalomarMonotiles.keys7Chunk11.map toInternal = SparseMonotiles.keys7Chunk11 := rfl

theorem keys7Chunk12_eq :
    PalomarMonotiles.keys7Chunk12.map toInternal = SparseMonotiles.keys7Chunk12 := rfl

theorem keys7Chunk13_eq :
    PalomarMonotiles.keys7Chunk13.map toInternal = SparseMonotiles.keys7Chunk13 := rfl

theorem keys7Chunk14_eq :
    PalomarMonotiles.keys7Chunk14.map toInternal = SparseMonotiles.keys7Chunk14 := rfl

theorem keys7Chunk15_eq :
    PalomarMonotiles.keys7Chunk15.map toInternal = SparseMonotiles.keys7Chunk15 := rfl

theorem keys7Chunk16_eq :
    PalomarMonotiles.keys7Chunk16.map toInternal = SparseMonotiles.keys7Chunk16 := rfl

theorem keys7Chunk17_eq :
    PalomarMonotiles.keys7Chunk17.map toInternal = SparseMonotiles.keys7Chunk17 := rfl

theorem keys7Chunk18_eq :
    PalomarMonotiles.keys7Chunk18.map toInternal = SparseMonotiles.keys7Chunk18 := rfl

theorem keys7Chunk19_eq :
    PalomarMonotiles.keys7Chunk19.map toInternal = SparseMonotiles.keys7Chunk19 := rfl

theorem keys7Chunk20_eq :
    PalomarMonotiles.keys7Chunk20.map toInternal = SparseMonotiles.keys7Chunk20 := rfl

theorem keys7Chunk21_eq :
    PalomarMonotiles.keys7Chunk21.map toInternal = SparseMonotiles.keys7Chunk21 := rfl

theorem keys7Chunk22_eq :
    PalomarMonotiles.keys7Chunk22.map toInternal = SparseMonotiles.keys7Chunk22 := rfl

theorem keys7Chunk23_eq :
    PalomarMonotiles.keys7Chunk23.map toInternal = SparseMonotiles.keys7Chunk23 := rfl

theorem keys7Chunk24_eq :
    PalomarMonotiles.keys7Chunk24.map toInternal = SparseMonotiles.keys7Chunk24 := rfl

theorem keys7Chunk25_eq :
    PalomarMonotiles.keys7Chunk25.map toInternal = SparseMonotiles.keys7Chunk25 := rfl

theorem keys7Chunk26_eq :
    PalomarMonotiles.keys7Chunk26.map toInternal = SparseMonotiles.keys7Chunk26 := rfl

theorem keys7Chunk27_eq :
    PalomarMonotiles.keys7Chunk27.map toInternal = SparseMonotiles.keys7Chunk27 := rfl

theorem keys7Chunk28_eq :
    PalomarMonotiles.keys7Chunk28.map toInternal = SparseMonotiles.keys7Chunk28 := rfl

theorem keys7Chunk29_eq :
    PalomarMonotiles.keys7Chunk29.map toInternal = SparseMonotiles.keys7Chunk29 := rfl

theorem keys7Chunk30_eq :
    PalomarMonotiles.keys7Chunk30.map toInternal = SparseMonotiles.keys7Chunk30 := rfl

theorem keys7Chunk31_eq :
    PalomarMonotiles.keys7Chunk31.map toInternal = SparseMonotiles.keys7Chunk31 := rfl

theorem keys7_eq :
    PalomarMonotiles.keys7.map toInternal = SparseMonotiles.keys7 := by
  simp only [PalomarMonotiles.keys7, SparseMonotiles.keys7, List.map_append,
    keys7Chunk0_eq,
    keys7Chunk1_eq,
    keys7Chunk2_eq,
    keys7Chunk3_eq,
    keys7Chunk4_eq,
    keys7Chunk5_eq,
    keys7Chunk6_eq,
    keys7Chunk7_eq,
    keys7Chunk8_eq,
    keys7Chunk9_eq,
    keys7Chunk10_eq,
    keys7Chunk11_eq,
    keys7Chunk12_eq,
    keys7Chunk13_eq,
    keys7Chunk14_eq,
    keys7Chunk15_eq,
    keys7Chunk16_eq,
    keys7Chunk17_eq,
    keys7Chunk18_eq,
    keys7Chunk19_eq,
    keys7Chunk20_eq,
    keys7Chunk21_eq,
    keys7Chunk22_eq,
    keys7Chunk23_eq,
    keys7Chunk24_eq,
    keys7Chunk25_eq,
    keys7Chunk26_eq,
    keys7Chunk27_eq,
    keys7Chunk28_eq,
    keys7Chunk29_eq,
    keys7Chunk30_eq,
    keys7Chunk31_eq]

theorem T7_eq : PalomarMonotiles.T7 = SparseMonotiles.T7 := by
  unfold PalomarMonotiles.T7 SparseMonotiles.T7
  rw [body_eq, keys7_eq]

theorem keys7_length : PalomarMonotiles.keys7.length = 1024 := rfl

theorem tiling_iff (tiles : Set (Set (PalomarMonotiles.Point 7))) :
    PalomarMonotiles.IsTiling PalomarMonotiles.T7 tiles ↔
      SparseMonotiles.IsTiling SparseMonotiles.T7 tiles := by
  change SparseMonotiles.IsTiling PalomarMonotiles.T7 tiles ↔ _
  rw [T7_eq]

#print axioms T7_eq
#print axioms keys7_length
#print axioms tiling_iff
end HENRY.Binding
