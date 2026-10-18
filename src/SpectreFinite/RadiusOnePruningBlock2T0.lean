module

public import SpectreFinite.RadiusOnePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_2_0 : List Verdict := [
  .keep ⟨(6,1),(7,3),(0,1),(3,1),(0,5),(1,5),(2,0)⟩,
  .reject ⟨(6,1),(8,3),(0,1),(3,1),(0,5),(1,5),(2,0)⟩ 3,
  .reject ⟨(6,1),(7,3),(0,1),(5,1),(0,5),(1,5),(2,0)⟩ 1,
  .reject ⟨(6,1),(8,3),(0,1),(5,1),(0,5),(1,5),(2,0)⟩ 1,
  .keep ⟨(0,4),(2,3),(0,1),(3,1),(0,5),(6,5),(2,0)⟩,
  .reject ⟨(0,4),(4,3),(0,1),(3,1),(0,5),(6,5),(2,0)⟩ 3,
  .reject ⟨(0,4),(2,3),(0,1),(5,1),(0,5),(6,5),(2,0)⟩ 1,
  .reject ⟨(0,4),(4,3),(0,1),(5,1),(0,5),(6,5),(2,0)⟩ 1
]
theorem check0_2_0 : checkRows trees0 rows0_2_0 = true := by decide
def rows1_2_0 : List Verdict := [
  .keep ⟨(6,1),(7,3),(0,1),(3,1),(0,5),(1,5),(2,0)⟩,
  .keep ⟨(0,4),(2,3),(0,1),(3,1),(0,5),(6,5),(2,0)⟩
]
theorem check1_2_0 : checkRows trees1 rows1_2_0 = true := by decide
theorem link1_2_0 : rows1_2_0.map Verdict.window = rows0_2_0.filterMap Verdict.kept := by rfl
def rows2_2_0 : List Verdict := [
  .keep ⟨(6,1),(7,3),(0,1),(3,1),(0,5),(1,5),(2,0)⟩,
  .keep ⟨(0,4),(2,3),(0,1),(3,1),(0,5),(6,5),(2,0)⟩
]
theorem check2_2_0 : checkRows trees2 rows2_2_0 = true := by decide
theorem link2_2_0 : rows2_2_0.map Verdict.window = rows1_2_0.filterMap Verdict.kept := by rfl
end SpectreFinite.HexSearch.SignaturePruning
