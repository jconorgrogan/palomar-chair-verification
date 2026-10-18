module

public import SpectreFinite.RadiusOnePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_3 : List Verdict := [
  .reject ⟨(7,5),(4,2),(1,2),(6,4),(4,2),(4,3),(3,3)⟩ 0,
  .reject ⟨(7,5),(4,2),(1,2),(6,4),(4,2),(5,3),(3,3)⟩ 0,
  .reject ⟨(7,5),(4,2),(1,2),(6,4),(4,2),(8,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(4,2),(1,2),(6,4),(4,2),(4,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(4,2),(1,2),(6,4),(4,2),(5,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(4,2),(1,2),(6,4),(4,2),(8,3),(3,3)⟩ 0,
  .keep ⟨(4,1),(5,2),(1,2),(6,4),(4,2),(0,3),(3,3)⟩,
  .reject ⟨(7,5),(8,2),(1,2),(6,4),(4,2),(4,3),(3,3)⟩ 0,
  .reject ⟨(7,5),(8,2),(1,2),(6,4),(4,2),(5,3),(3,3)⟩ 0,
  .reject ⟨(7,5),(8,2),(1,2),(6,4),(4,2),(8,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(8,2),(1,2),(6,4),(4,2),(4,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(8,2),(1,2),(6,4),(4,2),(5,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(8,2),(1,2),(6,4),(4,2),(8,3),(3,3)⟩ 0,
  .reject ⟨(7,5),(4,2),(6,2),(0,1),(2,2),(4,3),(3,3)⟩ 0,
  .reject ⟨(7,5),(4,2),(6,2),(0,1),(2,2),(5,3),(3,3)⟩ 0,
  .reject ⟨(7,5),(4,2),(6,2),(0,1),(2,2),(8,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(4,2),(6,2),(0,1),(2,2),(4,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(4,2),(6,2),(0,1),(2,2),(5,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(4,2),(6,2),(0,1),(2,2),(8,3),(3,3)⟩ 0,
  .keep ⟨(4,1),(5,2),(6,2),(0,1),(2,2),(0,3),(3,3)⟩,
  .reject ⟨(7,5),(8,2),(6,2),(0,1),(2,2),(4,3),(3,3)⟩ 0,
  .reject ⟨(7,5),(8,2),(6,2),(0,1),(2,2),(5,3),(3,3)⟩ 0,
  .reject ⟨(7,5),(8,2),(6,2),(0,1),(2,2),(8,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(8,2),(6,2),(0,1),(2,2),(4,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(8,2),(6,2),(0,1),(2,2),(5,3),(3,3)⟩ 0,
  .reject ⟨(8,5),(8,2),(6,2),(0,1),(2,2),(8,3),(3,3)⟩ 0
]
theorem check0_3_3 : checkRows trees0 rows0_3_3 = true := by decide
def rows1_3_3 : List Verdict := [
  .keep ⟨(4,1),(5,2),(1,2),(6,4),(4,2),(0,3),(3,3)⟩,
  .keep ⟨(4,1),(5,2),(6,2),(0,1),(2,2),(0,3),(3,3)⟩
]
theorem check1_3_3 : checkRows trees1 rows1_3_3 = true := by decide
theorem link1_3_3 : rows1_3_3.map Verdict.window = rows0_3_3.filterMap Verdict.kept := by rfl
def rows2_3_3 : List Verdict := [
  .keep ⟨(4,1),(5,2),(1,2),(6,4),(4,2),(0,3),(3,3)⟩,
  .keep ⟨(4,1),(5,2),(6,2),(0,1),(2,2),(0,3),(3,3)⟩
]
theorem check2_3_3 : checkRows trees2 rows2_3_3 = true := by decide
theorem link2_3_3 : rows2_3_3.map Verdict.window = rows1_3_3.filterMap Verdict.kept := by rfl
end SpectreFinite.HexSearch.SignaturePruning
