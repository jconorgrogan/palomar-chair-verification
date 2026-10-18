module

public import SpectreFinite.RadiusOnePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_2_5 : List Verdict := [
  .keep ⟨(1,4),(6,0),(7,2),(0,0),(3,0),(0,4),(2,5)⟩,
  .reject ⟨(1,4),(6,0),(8,2),(0,0),(3,0),(0,4),(2,5)⟩ 2,
  .reject ⟨(1,4),(6,0),(7,2),(0,0),(5,0),(0,4),(2,5)⟩ 0,
  .reject ⟨(1,4),(6,0),(8,2),(0,0),(5,0),(0,4),(2,5)⟩ 0,
  .keep ⟨(6,4),(0,3),(2,2),(0,0),(3,0),(0,4),(2,5)⟩,
  .reject ⟨(6,4),(0,3),(4,2),(0,0),(3,0),(0,4),(2,5)⟩ 2,
  .reject ⟨(6,4),(0,3),(2,2),(0,0),(5,0),(0,4),(2,5)⟩ 0,
  .reject ⟨(6,4),(0,3),(4,2),(0,0),(5,0),(0,4),(2,5)⟩ 0
]
theorem check0_2_5 : checkRows trees0 rows0_2_5 = true := by decide
def rows1_2_5 : List Verdict := [
  .keep ⟨(1,4),(6,0),(7,2),(0,0),(3,0),(0,4),(2,5)⟩,
  .keep ⟨(6,4),(0,3),(2,2),(0,0),(3,0),(0,4),(2,5)⟩
]
theorem check1_2_5 : checkRows trees1 rows1_2_5 = true := by decide
theorem link1_2_5 : rows1_2_5.map Verdict.window = rows0_2_5.filterMap Verdict.kept := by rfl
def rows2_2_5 : List Verdict := [
  .keep ⟨(1,4),(6,0),(7,2),(0,0),(3,0),(0,4),(2,5)⟩,
  .keep ⟨(6,4),(0,3),(2,2),(0,0),(3,0),(0,4),(2,5)⟩
]
theorem check2_2_5 : checkRows trees2 rows2_2_5 = true := by decide
theorem link2_2_5 : rows2_2_5.map Verdict.window = rows1_2_5.filterMap Verdict.kept := by rfl
end SpectreFinite.HexSearch.SignaturePruning
