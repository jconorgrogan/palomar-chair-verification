module

public import SpectreFinite.RadiusOnePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_4 : List Verdict := [
  .reject ⟨(4,3),(1,3),(6,5),(4,3),(4,4),(7,0),(3,4)⟩ 1,
  .reject ⟨(4,3),(1,3),(6,5),(4,3),(5,4),(7,0),(3,4)⟩ 0,
  .reject ⟨(4,3),(1,3),(6,5),(4,3),(8,4),(7,0),(3,4)⟩ 0,
  .reject ⟨(4,3),(1,3),(6,5),(4,3),(4,4),(8,0),(3,4)⟩ 0,
  .reject ⟨(4,3),(1,3),(6,5),(4,3),(5,4),(8,0),(3,4)⟩ 0,
  .reject ⟨(4,3),(1,3),(6,5),(4,3),(8,4),(8,0),(3,4)⟩ 0,
  .keep ⟨(5,3),(1,3),(6,5),(4,3),(0,4),(4,2),(3,4)⟩,
  .reject ⟨(8,3),(1,3),(6,5),(4,3),(4,4),(7,0),(3,4)⟩ 1,
  .reject ⟨(8,3),(1,3),(6,5),(4,3),(5,4),(7,0),(3,4)⟩ 0,
  .reject ⟨(8,3),(1,3),(6,5),(4,3),(8,4),(7,0),(3,4)⟩ 0,
  .reject ⟨(8,3),(1,3),(6,5),(4,3),(4,4),(8,0),(3,4)⟩ 0,
  .reject ⟨(8,3),(1,3),(6,5),(4,3),(5,4),(8,0),(3,4)⟩ 1,
  .reject ⟨(8,3),(1,3),(6,5),(4,3),(8,4),(8,0),(3,4)⟩ 1,
  .reject ⟨(4,3),(6,3),(0,2),(2,3),(4,4),(7,0),(3,4)⟩ 1,
  .reject ⟨(4,3),(6,3),(0,2),(2,3),(5,4),(7,0),(3,4)⟩ 0,
  .reject ⟨(4,3),(6,3),(0,2),(2,3),(8,4),(7,0),(3,4)⟩ 0,
  .reject ⟨(4,3),(6,3),(0,2),(2,3),(4,4),(8,0),(3,4)⟩ 0,
  .reject ⟨(4,3),(6,3),(0,2),(2,3),(5,4),(8,0),(3,4)⟩ 0,
  .reject ⟨(4,3),(6,3),(0,2),(2,3),(8,4),(8,0),(3,4)⟩ 0,
  .keep ⟨(5,3),(6,3),(0,2),(2,3),(0,4),(4,2),(3,4)⟩,
  .reject ⟨(8,3),(6,3),(0,2),(2,3),(4,4),(7,0),(3,4)⟩ 1,
  .reject ⟨(8,3),(6,3),(0,2),(2,3),(5,4),(7,0),(3,4)⟩ 0,
  .reject ⟨(8,3),(6,3),(0,2),(2,3),(8,4),(7,0),(3,4)⟩ 0,
  .reject ⟨(8,3),(6,3),(0,2),(2,3),(4,4),(8,0),(3,4)⟩ 0,
  .reject ⟨(8,3),(6,3),(0,2),(2,3),(5,4),(8,0),(3,4)⟩ 1,
  .reject ⟨(8,3),(6,3),(0,2),(2,3),(8,4),(8,0),(3,4)⟩ 1
]
theorem check0_3_4 : checkRows trees0 rows0_3_4 = true := by decide
def rows1_3_4 : List Verdict := [
  .keep ⟨(5,3),(1,3),(6,5),(4,3),(0,4),(4,2),(3,4)⟩,
  .keep ⟨(5,3),(6,3),(0,2),(2,3),(0,4),(4,2),(3,4)⟩
]
theorem check1_3_4 : checkRows trees1 rows1_3_4 = true := by decide
theorem link1_3_4 : rows1_3_4.map Verdict.window = rows0_3_4.filterMap Verdict.kept := by rfl
def rows2_3_4 : List Verdict := [
  .keep ⟨(5,3),(1,3),(6,5),(4,3),(0,4),(4,2),(3,4)⟩,
  .keep ⟨(5,3),(6,3),(0,2),(2,3),(0,4),(4,2),(3,4)⟩
]
theorem check2_3_4 : checkRows trees2 rows2_3_4 = true := by decide
theorem link2_3_4 : rows2_3_4.map Verdict.window = rows1_3_4.filterMap Verdict.kept := by rfl
end SpectreFinite.HexSearch.SignaturePruning
