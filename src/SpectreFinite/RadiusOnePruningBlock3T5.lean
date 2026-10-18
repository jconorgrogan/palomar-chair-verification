module

public import SpectreFinite.RadiusOnePruningTrees

@[expose] public section

namespace SpectreFinite.HexSearch.SignaturePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def rows0_3_5 : List Verdict := [
  .reject ⟨(1,4),(6,0),(4,4),(4,5),(7,1),(4,4),(3,5)⟩ 2,
  .reject ⟨(1,4),(6,0),(4,4),(5,5),(7,1),(4,4),(3,5)⟩ 1,
  .reject ⟨(1,4),(6,0),(4,4),(8,5),(7,1),(4,4),(3,5)⟩ 1,
  .reject ⟨(1,4),(6,0),(4,4),(4,5),(8,1),(4,4),(3,5)⟩ 1,
  .reject ⟨(1,4),(6,0),(4,4),(5,5),(8,1),(4,4),(3,5)⟩ 1,
  .reject ⟨(1,4),(6,0),(4,4),(8,5),(8,1),(4,4),(3,5)⟩ 1,
  .keep ⟨(1,4),(6,0),(4,4),(0,5),(4,3),(5,4),(3,5)⟩,
  .reject ⟨(1,4),(6,0),(4,4),(4,5),(7,1),(8,4),(3,5)⟩ 2,
  .reject ⟨(1,4),(6,0),(4,4),(5,5),(7,1),(8,4),(3,5)⟩ 1,
  .reject ⟨(1,4),(6,0),(4,4),(8,5),(7,1),(8,4),(3,5)⟩ 1,
  .reject ⟨(1,4),(6,0),(4,4),(4,5),(8,1),(8,4),(3,5)⟩ 1,
  .reject ⟨(1,4),(6,0),(4,4),(5,5),(8,1),(8,4),(3,5)⟩ 2,
  .reject ⟨(1,4),(6,0),(4,4),(8,5),(8,1),(8,4),(3,5)⟩ 2,
  .reject ⟨(6,4),(0,3),(2,4),(4,5),(7,1),(4,4),(3,5)⟩ 2,
  .reject ⟨(6,4),(0,3),(2,4),(5,5),(7,1),(4,4),(3,5)⟩ 1,
  .reject ⟨(6,4),(0,3),(2,4),(8,5),(7,1),(4,4),(3,5)⟩ 1,
  .reject ⟨(6,4),(0,3),(2,4),(4,5),(8,1),(4,4),(3,5)⟩ 1,
  .reject ⟨(6,4),(0,3),(2,4),(5,5),(8,1),(4,4),(3,5)⟩ 1,
  .reject ⟨(6,4),(0,3),(2,4),(8,5),(8,1),(4,4),(3,5)⟩ 1,
  .keep ⟨(6,4),(0,3),(2,4),(0,5),(4,3),(5,4),(3,5)⟩,
  .reject ⟨(6,4),(0,3),(2,4),(4,5),(7,1),(8,4),(3,5)⟩ 2,
  .reject ⟨(6,4),(0,3),(2,4),(5,5),(7,1),(8,4),(3,5)⟩ 1,
  .reject ⟨(6,4),(0,3),(2,4),(8,5),(7,1),(8,4),(3,5)⟩ 1,
  .reject ⟨(6,4),(0,3),(2,4),(4,5),(8,1),(8,4),(3,5)⟩ 1,
  .reject ⟨(6,4),(0,3),(2,4),(5,5),(8,1),(8,4),(3,5)⟩ 2,
  .reject ⟨(6,4),(0,3),(2,4),(8,5),(8,1),(8,4),(3,5)⟩ 2
]
theorem check0_3_5 : checkRows trees0 rows0_3_5 = true := by decide
def rows1_3_5 : List Verdict := [
  .keep ⟨(1,4),(6,0),(4,4),(0,5),(4,3),(5,4),(3,5)⟩,
  .keep ⟨(6,4),(0,3),(2,4),(0,5),(4,3),(5,4),(3,5)⟩
]
theorem check1_3_5 : checkRows trees1 rows1_3_5 = true := by decide
theorem link1_3_5 : rows1_3_5.map Verdict.window = rows0_3_5.filterMap Verdict.kept := by rfl
def rows2_3_5 : List Verdict := [
  .keep ⟨(1,4),(6,0),(4,4),(0,5),(4,3),(5,4),(3,5)⟩,
  .keep ⟨(6,4),(0,3),(2,4),(0,5),(4,3),(5,4),(3,5)⟩
]
theorem check2_3_5 : checkRows trees2 rows2_3_5 = true := by decide
theorem link2_3_5 : rows2_3_5.map Verdict.window = rows1_3_5.filterMap Verdict.kept := by rfl
end SpectreFinite.HexSearch.SignaturePruning
