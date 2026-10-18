module

public import SpectreFinite.RadiusOnePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_1 : List Verdict := [
  .reject ⟨(4,0),(4,1),(7,3),(4,0),(1,0),(6,2),(3,1)⟩ 4,
  .reject ⟨(4,0),(5,1),(7,3),(4,0),(1,0),(6,2),(3,1)⟩ 3,
  .reject ⟨(4,0),(8,1),(7,3),(4,0),(1,0),(6,2),(3,1)⟩ 3,
  .reject ⟨(4,0),(4,1),(8,3),(4,0),(1,0),(6,2),(3,1)⟩ 3,
  .reject ⟨(4,0),(5,1),(8,3),(4,0),(1,0),(6,2),(3,1)⟩ 3,
  .reject ⟨(4,0),(8,1),(8,3),(4,0),(1,0),(6,2),(3,1)⟩ 3,
  .keep ⟨(4,0),(0,1),(4,5),(5,0),(1,0),(6,2),(3,1)⟩,
  .reject ⟨(4,0),(4,1),(7,3),(8,0),(1,0),(6,2),(3,1)⟩ 4,
  .reject ⟨(4,0),(5,1),(7,3),(8,0),(1,0),(6,2),(3,1)⟩ 3,
  .reject ⟨(4,0),(8,1),(7,3),(8,0),(1,0),(6,2),(3,1)⟩ 3,
  .reject ⟨(4,0),(4,1),(8,3),(8,0),(1,0),(6,2),(3,1)⟩ 3,
  .reject ⟨(4,0),(5,1),(8,3),(8,0),(1,0),(6,2),(3,1)⟩ 4,
  .reject ⟨(4,0),(8,1),(8,3),(8,0),(1,0),(6,2),(3,1)⟩ 4,
  .reject ⟨(2,0),(4,1),(7,3),(4,0),(6,0),(0,5),(3,1)⟩ 4,
  .reject ⟨(2,0),(5,1),(7,3),(4,0),(6,0),(0,5),(3,1)⟩ 3,
  .reject ⟨(2,0),(8,1),(7,3),(4,0),(6,0),(0,5),(3,1)⟩ 3,
  .reject ⟨(2,0),(4,1),(8,3),(4,0),(6,0),(0,5),(3,1)⟩ 3,
  .reject ⟨(2,0),(5,1),(8,3),(4,0),(6,0),(0,5),(3,1)⟩ 3,
  .reject ⟨(2,0),(8,1),(8,3),(4,0),(6,0),(0,5),(3,1)⟩ 3,
  .keep ⟨(2,0),(0,1),(4,5),(5,0),(6,0),(0,5),(3,1)⟩,
  .reject ⟨(2,0),(4,1),(7,3),(8,0),(6,0),(0,5),(3,1)⟩ 4,
  .reject ⟨(2,0),(5,1),(7,3),(8,0),(6,0),(0,5),(3,1)⟩ 3,
  .reject ⟨(2,0),(8,1),(7,3),(8,0),(6,0),(0,5),(3,1)⟩ 3,
  .reject ⟨(2,0),(4,1),(8,3),(8,0),(6,0),(0,5),(3,1)⟩ 3,
  .reject ⟨(2,0),(5,1),(8,3),(8,0),(6,0),(0,5),(3,1)⟩ 4,
  .reject ⟨(2,0),(8,1),(8,3),(8,0),(6,0),(0,5),(3,1)⟩ 4
]
theorem check0_3_1 : checkRows trees0 rows0_3_1 = true := by decide
def rows1_3_1 : List Verdict := [
  .keep ⟨(4,0),(0,1),(4,5),(5,0),(1,0),(6,2),(3,1)⟩,
  .keep ⟨(2,0),(0,1),(4,5),(5,0),(6,0),(0,5),(3,1)⟩
]
theorem check1_3_1 : checkRows trees1 rows1_3_1 = true := by decide
theorem link1_3_1 : rows1_3_1.map Verdict.window = rows0_3_1.filterMap Verdict.kept := by rfl
def rows2_3_1 : List Verdict := [
  .keep ⟨(4,0),(0,1),(4,5),(5,0),(1,0),(6,2),(3,1)⟩,
  .keep ⟨(2,0),(0,1),(4,5),(5,0),(6,0),(0,5),(3,1)⟩
]
theorem check2_3_1 : checkRows trees2 rows2_3_1 = true := by decide
theorem link2_3_1 : rows2_3_1.map Verdict.window = rows1_3_1.filterMap Verdict.kept := by rfl
end SpectreFinite.HexSearch.SignaturePruning
