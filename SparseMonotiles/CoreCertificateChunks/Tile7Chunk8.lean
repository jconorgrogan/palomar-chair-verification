module

public import SparseMonotiles.CellCores
public import SparseMonotiles.Tile7Data

@[expose] public section

namespace SparseMonotiles

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem keys7Chunk8_normalBand : ∀ k ∈ keys7Chunk8, HasNormalIntegerBand (1/100) k := by
  intro k hk
  simp only [keys7Chunk8, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨⟨0, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨1, by decide⟩, 2, ?_⟩
    change (0 : ℚ) = 0 ∧ (2 : ℚ) = ((2 : ℤ) : ℚ) ∧ |((671/336) : ℚ) - ((2 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨1, by decide⟩, 2, ?_⟩
    change (0 : ℚ) = 0 ∧ (2 : ℚ) = ((2 : ℤ) : ℚ) ∧ |((673/336) : ℚ) - ((2 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨2, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨3, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨4, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨5, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨6, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨0, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨0, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨1, by decide⟩, 2, ?_⟩
    change (0 : ℚ) = 0 ∧ (2 : ℚ) = ((2 : ℤ) : ℚ) ∧ |((673/336) : ℚ) - ((2 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨2, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨3, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨4, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨5, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨6, by decide⟩, 2, ?_⟩
    change (0 : ℚ) = 0 ∧ (2 : ℚ) = ((2 : ℤ) : ℚ) ∧ |((671/336) : ℚ) - ((2 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨0, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨1, by decide⟩, 2, ?_⟩
    change (0 : ℚ) = 0 ∧ (2 : ℚ) = ((2 : ℤ) : ℚ) ∧ |((671/336) : ℚ) - ((2 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨2, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨3, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨3, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨4, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨5, by decide⟩, 2, ?_⟩
    change (0 : ℚ) = 0 ∧ (2 : ℚ) = ((2 : ℤ) : ℚ) ∧ |((673/336) : ℚ) - ((2 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨6, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨0, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨1, by decide⟩, 2, ?_⟩
    change (0 : ℚ) = 0 ∧ (2 : ℚ) = ((2 : ℤ) : ℚ) ∧ |((671/336) : ℚ) - ((2 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨2, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨3, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨4, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((-1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨4, by decide⟩, 0, ?_⟩
    change (0 : ℚ) = 0 ∧ (0 : ℚ) = ((0 : ℤ) : ℚ) ∧ |((1/336) : ℚ) - ((0 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨5, by decide⟩, 2, ?_⟩
    change (0 : ℚ) = 0 ∧ (2 : ℚ) = ((2 : ℤ) : ℚ) ∧ |((671/336) : ℚ) - ((2 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]
  · refine ⟨⟨6, by decide⟩, 2, ?_⟩
    change (0 : ℚ) = 0 ∧ (2 : ℚ) = ((2 : ℤ) : ℚ) ∧ |((671/336) : ℚ) - ((2 : ℤ) : ℚ)| ≤ 1/100
    norm_num [abs_le]

#print axioms keys7Chunk8_normalBand

end SparseMonotiles
