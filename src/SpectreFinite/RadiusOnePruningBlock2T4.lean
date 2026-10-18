module

public import SpectreFinite.RadiusOnePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_2_4 : List Verdict := [
  .keep ⟨(0,3),(1,3),(6,5),(7,1),(0,5),(3,5),(2,4)⟩,
  .reject ⟨(0,3),(1,3),(6,5),(8,1),(0,5),(3,5),(2,4)⟩ 1,
  .reject ⟨(0,3),(1,3),(6,5),(7,1),(0,5),(5,5),(2,4)⟩ 0,
  .reject ⟨(0,3),(1,3),(6,5),(8,1),(0,5),(5,5),(2,4)⟩ 0,
  .keep ⟨(0,3),(6,3),(0,2),(2,1),(0,5),(3,5),(2,4)⟩,
  .reject ⟨(0,3),(6,3),(0,2),(4,1),(0,5),(3,5),(2,4)⟩ 1,
  .reject ⟨(0,3),(6,3),(0,2),(2,1),(0,5),(5,5),(2,4)⟩ 0,
  .reject ⟨(0,3),(6,3),(0,2),(4,1),(0,5),(5,5),(2,4)⟩ 0
]
theorem check0_2_4 : checkRows trees0 rows0_2_4 = true := by decide
def rows1_2_4 : List Verdict := [
  .keep ⟨(0,3),(1,3),(6,5),(7,1),(0,5),(3,5),(2,4)⟩,
  .keep ⟨(0,3),(6,3),(0,2),(2,1),(0,5),(3,5),(2,4)⟩
]
theorem check1_2_4 : checkRows trees1 rows1_2_4 = true := by decide
theorem link1_2_4 : rows1_2_4.map Verdict.window = rows0_2_4.filterMap Verdict.kept := by rfl
def rows2_2_4 : List Verdict := [
  .keep ⟨(0,3),(1,3),(6,5),(7,1),(0,5),(3,5),(2,4)⟩,
  .keep ⟨(0,3),(6,3),(0,2),(2,1),(0,5),(3,5),(2,4)⟩
]
theorem check2_2_4 : checkRows trees2 rows2_2_4 = true := by decide
theorem link2_2_4 : rows2_2_4.map Verdict.window = rows1_2_4.filterMap Verdict.kept := by rfl
end SpectreFinite.HexSearch.SignaturePruning
