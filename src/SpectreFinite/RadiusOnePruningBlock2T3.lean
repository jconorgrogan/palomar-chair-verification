module

public import SpectreFinite.RadiusOnePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_2_3 : List Verdict := [
  .keep ⟨(3,4),(0,2),(1,2),(6,4),(7,0),(0,4),(2,3)⟩,
  .reject ⟨(3,4),(0,2),(1,2),(6,4),(8,0),(0,4),(2,3)⟩ 0,
  .reject ⟨(5,4),(0,2),(1,2),(6,4),(7,0),(0,4),(2,3)⟩ 4,
  .reject ⟨(5,4),(0,2),(1,2),(6,4),(8,0),(0,4),(2,3)⟩ 0,
  .keep ⟨(3,4),(0,2),(6,2),(0,1),(2,0),(0,4),(2,3)⟩,
  .reject ⟨(3,4),(0,2),(6,2),(0,1),(4,0),(0,4),(2,3)⟩ 0,
  .reject ⟨(5,4),(0,2),(6,2),(0,1),(2,0),(0,4),(2,3)⟩ 4,
  .reject ⟨(5,4),(0,2),(6,2),(0,1),(4,0),(0,4),(2,3)⟩ 0
]
theorem check0_2_3 : checkRows trees0 rows0_2_3 = true := by decide
def rows1_2_3 : List Verdict := [
  .keep ⟨(3,4),(0,2),(1,2),(6,4),(7,0),(0,4),(2,3)⟩,
  .keep ⟨(3,4),(0,2),(6,2),(0,1),(2,0),(0,4),(2,3)⟩
]
theorem check1_2_3 : checkRows trees1 rows1_2_3 = true := by decide
theorem link1_2_3 : rows1_2_3.map Verdict.window = rows0_2_3.filterMap Verdict.kept := by rfl
def rows2_2_3 : List Verdict := [
  .keep ⟨(3,4),(0,2),(1,2),(6,4),(7,0),(0,4),(2,3)⟩,
  .keep ⟨(3,4),(0,2),(6,2),(0,1),(2,0),(0,4),(2,3)⟩
]
theorem check2_2_3 : checkRows trees2 rows2_2_3 = true := by decide
theorem link2_2_3 : rows2_2_3.map Verdict.window = rows1_2_3.filterMap Verdict.kept := by rfl
end SpectreFinite.HexSearch.SignaturePruning
