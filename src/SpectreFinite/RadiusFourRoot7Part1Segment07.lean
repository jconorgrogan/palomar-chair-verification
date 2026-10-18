module

public import SpectreFinite.RadiusFourRoot7Part1Segment06
public import SpectreFinite.RadiusFourRoot7Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable1
public import SpectreFinite.RadiusFourTable20
public import SpectreFinite.RadiusFourTable31
public import SpectreFinite.RadiusFourTable46
public import SpectreFinite.RadiusFourTable7

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root7Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3_checked :
    checkReplacement table46 root7Node1Domains2 root7Node1Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node1Step3Chunk0_0_checked, root7Node1Step3Chunk0_1_checked, root7Node1Step3Chunk0_2_checked, root7Node1Step3Chunk0_3_checked, root7Node1Step3Chunk0_4_checked, root7Node1Step3Chunk0_5_checked, root7Node1Step3Chunk1_0_checked, root7Node1Step3Chunk1_1_checked, root7Node1Step3Chunk1_2_checked, root7Node1Step3Chunk1_3_checked, root7Node1Step3Chunk1_4_checked, root7Node1Step3Chunk1_5_checked, root7Node1Step3Chunk2_0_checked, root7Node1Step3Chunk2_1_checked, root7Node1Step3Chunk2_2_checked, root7Node1Step3Chunk2_3_checked, root7Node1Step3Chunk2_4_checked, root7Node1Step3Chunk2_5_checked, root7Node1Step3Chunk3_0_checked, root7Node1Step3Chunk3_1_checked, root7Node1Step3Chunk3_2_checked, root7Node1Step3Chunk3_3_checked, root7Node1Step3Chunk3_4_checked, root7Node1Step3Chunk3_5_checked, root7Node1Step3Chunk4_0_checked, root7Node1Step3Chunk4_1_checked, root7Node1Step3Chunk4_2_checked, root7Node1Step3Chunk4_3_checked, root7Node1Step3Chunk4_4_checked, root7Node1Step3Chunk4_5_checked, root7Node1Step3Chunk5_0_checked, root7Node1Step3Chunk5_1_checked, root7Node1Step3Chunk5_2_checked, root7Node1Step3Chunk5_3_checked, root7Node1Step3Chunk5_4_checked, root7Node1Step3Chunk5_5_checked, root7Node1Step3Chunk6_0_checked, root7Node1Step3Chunk6_1_checked, root7Node1Step3Chunk6_2_checked, root7Node1Step3Chunk6_3_checked, root7Node1Step3Chunk6_4_checked, root7Node1Step3Chunk6_5_checked, root7Node1Step3Chunk7_0_checked, root7Node1Step3Chunk7_1_checked, root7Node1Step3Chunk7_2_checked, root7Node1Step3Chunk7_3_checked, root7Node1Step3Chunk7_4_checked, root7Node1Step3Chunk7_5_checked, root7Node1Step3Chunk8_0_checked, root7Node1Step3Chunk8_1_checked, root7Node1Step3Chunk8_2_checked, root7Node1Step3Chunk8_3_checked, root7Node1Step3Chunk8_4_checked, root7Node1Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node1Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,1),(5,1),(7,5),(8,1)]
  | 1 => [(0,1),(0,2),(6,0),(6,5)]
  | 2 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 3 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 4 => [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 5 => [(7,3),(8,3)]
  | 6 => [(5,2),(5,5),(8,2)]
  | 7 => [(1,0),(3,0),(5,0)]
  | 8 => [(2,1),(2,5),(4,5)]
  | 9 => [(0,2),(1,0),(6,0),(7,0)]
  | 10 => [(1,1),(4,3),(7,1),(8,3)]
  | 11 => [(0,1),(1,4),(6,4)]
  | 12 => [(0,5),(1,2),(6,2)]
  | 13 => [(4,4),(8,4)]
  | 14 => [(0,0)]
  | 15 => [(3,2),(7,2)]
  | 16 => [(4,0),(7,4)]
  | 17 => [(1,3),(7,3)]
  | 18 => [(7,5),(8,5)]
  | 19 => [(0,3),(1,0),(6,0)]
  | 20 => [(7,1),(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1),(8,1)]
  | 24 => [(0,1),(6,5)]
  | 25 => [(0,4),(6,2)]
  | 26 => [(1,3),(7,3)]
  | 27 => [(4,2),(8,2)]
  | 28 => [(5,0),(5,3)]
  | 29 => [(4,5),(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5),(8,5)]
  | 33 => [(1,0),(3,0),(7,0)]
  | 34 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 35 => [(0,4),(1,2),(6,2)]
  | 36 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 37 => [(0,0),(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(1,3),(6,3)]
  | 41 => [(4,4),(7,2),(8,2)]
  | 42 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 43 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 44 => [(0,2),(1,5),(6,0)]
  | 45 => [(1,1),(6,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(7,1)]
  | 49 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 50 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 51 => [(2,0),(4,0),(7,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5),(8,2),(8,5)]
  | 54 => [(5,0),(7,0),(8,0)]
  | 55 => [(4,3),(4,5),(7,3),(8,3)]
  | 56 => [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 57 => [(0,1),(1,4),(7,4)]
  | 58 => [(0,5),(6,2),(6,3)]
  | 59 => [(4,4),(7,2),(8,4)]
  | _ => [(0,0),(1,4),(6,4),(7,4)]
def root7Node1Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1),(5,1),(7,5),(8,1)]
  | 1 => some [(0,1),(0,2),(6,0),(6,5)]
  | 2 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 3 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 4 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 5 => some [(7,3),(8,3)]
  | 6 => some [(5,2),(5,5),(8,2)]
  | 7 => some [(1,0),(3,0),(5,0)]
  | 8 => some [(2,1),(2,5),(4,5)]
  | 9 => some [(0,2),(1,0),(6,0),(7,0)]
  | 10 => some [(1,1),(4,3),(7,1),(8,3)]
  | 11 => some [(0,1),(1,4),(6,4)]
  | 12 => some [(0,5),(1,2),(6,2)]
  | 13 => some [(4,4),(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(3,2),(7,2)]
  | 16 => some [(4,0),(7,4)]
  | 17 => some [(1,3),(7,3)]
  | 18 => some [(7,5),(8,5)]
  | 19 => some [(0,3),(1,0),(6,0)]
  | 20 => some [(7,1),(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1),(8,1)]
  | 24 => some [(0,1),(6,5)]
  | 25 => some [(0,4),(6,2)]
  | 26 => some [(1,3),(7,3)]
  | 27 => some [(4,2),(8,2)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5),(8,5)]
  | 33 => some [(1,0),(3,0),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 35 => some [(0,4),(1,2),(6,2)]
  | 36 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 37 => some [(0,0),(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(4,4),(7,2),(8,2)]
  | 42 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 44 => some [(0,2),(1,5),(6,0)]
  | 45 => some [(1,1),(6,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(7,1)]
  | 49 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 50 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 51 => some [(2,0),(4,0),(7,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2),(8,5)]
  | 54 => some [(5,0),(7,0),(8,0)]
  | 55 => some [(4,3),(4,5),(7,3),(8,3)]
  | 56 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 57 => some [(0,1),(1,4),(7,4)]
  | 58 => some [(0,5),(6,2),(6,3)]
  | 59 => some [(4,4),(7,2),(8,4)]
  | _ => some [(0,0),(1,4),(6,4),(7,4)]
theorem root7Node1Domains4_fast_eq : root7Node1Domains4 = expandDomains root7Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node1Domains4 v = expandDomains root7Node1Domains4Fast v from by decide) v
theorem root7Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFour
