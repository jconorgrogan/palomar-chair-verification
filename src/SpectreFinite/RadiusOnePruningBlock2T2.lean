module

public import SpectreFinite.RadiusOnePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_2_2 : List Verdict := [
  .keep ⟨(0,3),(3,3),(0,1),(1,1),(6,3),(7,5),(2,2)⟩,
  .reject ⟨(0,3),(3,3),(0,1),(1,1),(6,3),(8,5),(2,2)⟩ 0,
  .reject ⟨(0,3),(5,3),(0,1),(1,1),(6,3),(7,5),(2,2)⟩ 3,
  .reject ⟨(0,3),(5,3),(0,1),(1,1),(6,3),(8,5),(2,2)⟩ 0,
  .keep ⟨(0,3),(3,3),(0,1),(6,1),(0,0),(2,5),(2,2)⟩,
  .reject ⟨(0,3),(3,3),(0,1),(6,1),(0,0),(4,5),(2,2)⟩ 0,
  .reject ⟨(0,3),(5,3),(0,1),(6,1),(0,0),(2,5),(2,2)⟩ 3,
  .reject ⟨(0,3),(5,3),(0,1),(6,1),(0,0),(4,5),(2,2)⟩ 0
]
theorem check0_2_2 : checkRows trees0 rows0_2_2 = true := by decide
def rows1_2_2 : List Verdict := [
  .keep ⟨(0,3),(3,3),(0,1),(1,1),(6,3),(7,5),(2,2)⟩,
  .keep ⟨(0,3),(3,3),(0,1),(6,1),(0,0),(2,5),(2,2)⟩
]
theorem check1_2_2 : checkRows trees1 rows1_2_2 = true := by decide
theorem link1_2_2 : rows1_2_2.map Verdict.window = rows0_2_2.filterMap Verdict.kept := by rfl
def rows2_2_2 : List Verdict := [
  .keep ⟨(0,3),(3,3),(0,1),(1,1),(6,3),(7,5),(2,2)⟩,
  .keep ⟨(0,3),(3,3),(0,1),(6,1),(0,0),(2,5),(2,2)⟩
]
theorem check2_2_2 : checkRows trees2 rows2_2_2 = true := by decide
theorem link2_2_2 : rows2_2_2.map Verdict.window = rows1_2_2.filterMap Verdict.kept := by rfl
end SpectreFinite.HexSearch.SignaturePruning
