module

public import SpectreFinite.RadiusOnePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_2_1 : List Verdict := [
  .keep ⟨(7,4),(0,2),(3,2),(0,0),(1,0),(6,2),(2,1)⟩,
  .reject ⟨(8,4),(0,2),(3,2),(0,0),(1,0),(6,2),(2,1)⟩ 4,
  .reject ⟨(7,4),(0,2),(5,2),(0,0),(1,0),(6,2),(2,1)⟩ 2,
  .reject ⟨(8,4),(0,2),(5,2),(0,0),(1,0),(6,2),(2,1)⟩ 2,
  .keep ⟨(2,4),(0,2),(3,2),(0,0),(6,0),(0,5),(2,1)⟩,
  .reject ⟨(4,4),(0,2),(3,2),(0,0),(6,0),(0,5),(2,1)⟩ 4,
  .reject ⟨(2,4),(0,2),(5,2),(0,0),(6,0),(0,5),(2,1)⟩ 2,
  .reject ⟨(4,4),(0,2),(5,2),(0,0),(6,0),(0,5),(2,1)⟩ 2
]
theorem check0_2_1 : checkRows trees0 rows0_2_1 = true := by decide
def rows1_2_1 : List Verdict := [
  .keep ⟨(7,4),(0,2),(3,2),(0,0),(1,0),(6,2),(2,1)⟩,
  .keep ⟨(2,4),(0,2),(3,2),(0,0),(6,0),(0,5),(2,1)⟩
]
theorem check1_2_1 : checkRows trees1 rows1_2_1 = true := by decide
theorem link1_2_1 : rows1_2_1.map Verdict.window = rows0_2_1.filterMap Verdict.kept := by rfl
def rows2_2_1 : List Verdict := [
  .keep ⟨(7,4),(0,2),(3,2),(0,0),(1,0),(6,2),(2,1)⟩,
  .keep ⟨(2,4),(0,2),(3,2),(0,0),(6,0),(0,5),(2,1)⟩
]
theorem check2_2_1 : checkRows trees2 rows2_2_1 = true := by decide
theorem link2_2_1 : rows2_2_1.map Verdict.window = rows1_2_1.filterMap Verdict.kept := by rfl
end SpectreFinite.HexSearch.SignaturePruning
