module

public import SpectreFinite.RadiusOnePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_2 : List Verdict := [
  .reject ⟨(4,2),(7,4),(4,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .reject ⟨(5,2),(7,4),(4,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .reject ⟨(8,2),(7,4),(4,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .reject ⟨(4,2),(8,4),(4,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .reject ⟨(5,2),(8,4),(4,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .reject ⟨(8,2),(8,4),(4,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .keep ⟨(0,2),(4,0),(5,1),(1,1),(6,3),(4,1),(3,2)⟩,
  .reject ⟨(4,2),(7,4),(8,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .reject ⟨(5,2),(7,4),(8,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .reject ⟨(8,2),(7,4),(8,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .reject ⟨(4,2),(8,4),(8,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .reject ⟨(5,2),(8,4),(8,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .reject ⟨(8,2),(8,4),(8,1),(1,1),(6,3),(4,1),(3,2)⟩ 0,
  .reject ⟨(4,2),(7,4),(4,1),(6,1),(0,0),(2,1),(3,2)⟩ 0,
  .reject ⟨(5,2),(7,4),(4,1),(6,1),(0,0),(2,1),(3,2)⟩ 0,
  .reject ⟨(8,2),(7,4),(4,1),(6,1),(0,0),(2,1),(3,2)⟩ 0,
  .reject ⟨(4,2),(8,4),(4,1),(6,1),(0,0),(2,1),(3,2)⟩ 0,
  .reject ⟨(5,2),(8,4),(4,1),(6,1),(0,0),(2,1),(3,2)⟩ 0,
  .reject ⟨(8,2),(8,4),(4,1),(6,1),(0,0),(2,1),(3,2)⟩ 0,
  .keep ⟨(0,2),(4,0),(5,1),(6,1),(0,0),(2,1),(3,2)⟩,
  .reject ⟨(4,2),(7,4),(8,1),(6,1),(0,0),(2,1),(3,2)⟩ 0,
  .reject ⟨(5,2),(7,4),(8,1),(6,1),(0,0),(2,1),(3,2)⟩ 0,
  .reject ⟨(8,2),(7,4),(8,1),(6,1),(0,0),(2,1),(3,2)⟩ 0,
  .reject ⟨(4,2),(8,4),(8,1),(6,1),(0,0),(2,1),(3,2)⟩ 0,
  .reject ⟨(5,2),(8,4),(8,1),(6,1),(0,0),(2,1),(3,2)⟩ 0,
  .reject ⟨(8,2),(8,4),(8,1),(6,1),(0,0),(2,1),(3,2)⟩ 0
]
theorem check0_3_2 : checkRows trees0 rows0_3_2 = true := by decide
def rows1_3_2 : List Verdict := [
  .keep ⟨(0,2),(4,0),(5,1),(1,1),(6,3),(4,1),(3,2)⟩,
  .keep ⟨(0,2),(4,0),(5,1),(6,1),(0,0),(2,1),(3,2)⟩
]
theorem check1_3_2 : checkRows trees1 rows1_3_2 = true := by decide
theorem link1_3_2 : rows1_3_2.map Verdict.window = rows0_3_2.filterMap Verdict.kept := by rfl
def rows2_3_2 : List Verdict := [
  .keep ⟨(0,2),(4,0),(5,1),(1,1),(6,3),(4,1),(3,2)⟩,
  .keep ⟨(0,2),(4,0),(5,1),(6,1),(0,0),(2,1),(3,2)⟩
]
theorem check2_3_2 : checkRows trees2 rows2_3_2 = true := by decide
theorem link2_3_2 : rows2_3_2.map Verdict.window = rows1_3_2.filterMap Verdict.kept := by rfl
end SpectreFinite.HexSearch.SignaturePruning
