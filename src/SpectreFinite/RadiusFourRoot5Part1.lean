module

public import SpectreFinite.RadiusFourRoot5Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable1
public import SpectreFinite.RadiusFourTable2
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable4
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node1Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => [(0,4),(1,1),(6,1),(7,1)]
  | 2 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => [(1,2),(3,2),(5,2),(7,2)]
  | 6 => [(4,0),(8,0)]
  | 7 => [(7,3),(8,3)]
  | 8 => [(5,2),(5,5),(8,2)]
  | 9 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 10 => [(2,1),(2,5),(4,1),(4,5)]
  | 11 => [(0,3),(0,4),(6,1)]
  | 12 => [(5,1),(5,4)]
  | 13 => [(0,1),(1,4)]
  | 14 => [(0,5),(6,2)]
  | 15 => [(4,4),(8,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2),(7,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(4,3),(5,3),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(1,0),(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => [(0,0),(0,5),(6,0),(6,3)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node1Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 3 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(1,2),(3,2),(5,2),(7,2)]
  | 6 => some [(4,0),(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2)]
  | 9 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1),(4,5)]
  | 11 => some [(0,3),(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(4,3),(5,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => some [(0,0),(0,5),(6,0),(6,3)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node1Domains2_fast_eq : root5Node1Domains2 = expandDomains root5Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node1Domains2 v = expandDomains root5Node1Domains2Fast v from by decide) v
theorem root5Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2_checked :
    checkReplacement table40 root5Node1Domains1 root5Node1Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node1Step2Chunk0_0_checked, root5Node1Step2Chunk0_1_checked, root5Node1Step2Chunk0_2_checked, root5Node1Step2Chunk0_3_checked, root5Node1Step2Chunk0_4_checked, root5Node1Step2Chunk0_5_checked, root5Node1Step2Chunk1_0_checked, root5Node1Step2Chunk1_1_checked, root5Node1Step2Chunk1_2_checked, root5Node1Step2Chunk1_3_checked, root5Node1Step2Chunk1_4_checked, root5Node1Step2Chunk1_5_checked, root5Node1Step2Chunk2_0_checked, root5Node1Step2Chunk2_1_checked, root5Node1Step2Chunk2_2_checked, root5Node1Step2Chunk2_3_checked, root5Node1Step2Chunk2_4_checked, root5Node1Step2Chunk2_5_checked, root5Node1Step2Chunk3_0_checked, root5Node1Step2Chunk3_1_checked, root5Node1Step2Chunk3_2_checked, root5Node1Step2Chunk3_3_checked, root5Node1Step2Chunk3_4_checked, root5Node1Step2Chunk3_5_checked, root5Node1Step2Chunk4_0_checked, root5Node1Step2Chunk4_1_checked, root5Node1Step2Chunk4_2_checked, root5Node1Step2Chunk4_3_checked, root5Node1Step2Chunk4_4_checked, root5Node1Step2Chunk4_5_checked, root5Node1Step2Chunk5_0_checked, root5Node1Step2Chunk5_1_checked, root5Node1Step2Chunk5_2_checked, root5Node1Step2Chunk5_3_checked, root5Node1Step2Chunk5_4_checked, root5Node1Step2Chunk5_5_checked, root5Node1Step2Chunk6_0_checked, root5Node1Step2Chunk6_1_checked, root5Node1Step2Chunk6_2_checked, root5Node1Step2Chunk6_3_checked, root5Node1Step2Chunk6_4_checked, root5Node1Step2Chunk6_5_checked, root5Node1Step2Chunk7_0_checked, root5Node1Step2Chunk7_1_checked, root5Node1Step2Chunk7_2_checked, root5Node1Step2Chunk7_3_checked, root5Node1Step2Chunk7_4_checked, root5Node1Step2Chunk7_5_checked, root5Node1Step2Chunk8_0_checked, root5Node1Step2Chunk8_1_checked, root5Node1Step2Chunk8_2_checked, root5Node1Step2Chunk8_3_checked, root5Node1Step2Chunk8_4_checked, root5Node1Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node1Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(6,0)]
  | 1 => [(1,1),(7,1)]
  | 2 => [(4,1),(5,1),(7,5),(8,1)]
  | 3 => [(0,1),(0,2),(6,0),(6,5)]
  | 4 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 5 => [(1,2),(3,2),(5,2),(7,2)]
  | 6 => [(4,0),(8,0)]
  | 7 => [(7,3),(8,3)]
  | 8 => [(5,2),(5,5),(8,2)]
  | 9 => [(1,0),(3,0),(5,0)]
  | 10 => [(2,1),(2,5),(4,5)]
  | 11 => [(0,3),(0,4),(6,1)]
  | 12 => [(5,1),(5,4)]
  | 13 => [(0,1),(1,4)]
  | 14 => [(0,5),(6,2)]
  | 15 => [(4,4),(8,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2),(7,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(4,3),(5,3),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(1,0),(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => [(0,0),(0,5),(6,0),(6,3)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node1Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(6,0)]
  | 1 => some [(1,1),(7,1)]
  | 2 => some [(4,1),(5,1),(7,5),(8,1)]
  | 3 => some [(0,1),(0,2),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 5 => some [(1,2),(3,2),(5,2),(7,2)]
  | 6 => some [(4,0),(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2)]
  | 9 => some [(1,0),(3,0),(5,0)]
  | 10 => some [(2,1),(2,5),(4,5)]
  | 11 => some [(0,3),(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(4,3),(5,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 57 => some [(0,0),(0,5),(6,0),(6,3)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node1Domains3_fast_eq : root5Node1Domains3 = expandDomains root5Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node1Domains3 v = expandDomains root5Node1Domains3Fast v from by decide) v
theorem root5Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3_checked :
    checkReplacement table2 root5Node1Domains2 root5Node1Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node1Step3Chunk0_0_checked, root5Node1Step3Chunk0_1_checked, root5Node1Step3Chunk0_2_checked, root5Node1Step3Chunk0_3_checked, root5Node1Step3Chunk0_4_checked, root5Node1Step3Chunk0_5_checked, root5Node1Step3Chunk1_0_checked, root5Node1Step3Chunk1_1_checked, root5Node1Step3Chunk1_2_checked, root5Node1Step3Chunk1_3_checked, root5Node1Step3Chunk1_4_checked, root5Node1Step3Chunk1_5_checked, root5Node1Step3Chunk2_0_checked, root5Node1Step3Chunk2_1_checked, root5Node1Step3Chunk2_2_checked, root5Node1Step3Chunk2_3_checked, root5Node1Step3Chunk2_4_checked, root5Node1Step3Chunk2_5_checked, root5Node1Step3Chunk3_0_checked, root5Node1Step3Chunk3_1_checked, root5Node1Step3Chunk3_2_checked, root5Node1Step3Chunk3_3_checked, root5Node1Step3Chunk3_4_checked, root5Node1Step3Chunk3_5_checked, root5Node1Step3Chunk4_0_checked, root5Node1Step3Chunk4_1_checked, root5Node1Step3Chunk4_2_checked, root5Node1Step3Chunk4_3_checked, root5Node1Step3Chunk4_4_checked, root5Node1Step3Chunk4_5_checked, root5Node1Step3Chunk5_0_checked, root5Node1Step3Chunk5_1_checked, root5Node1Step3Chunk5_2_checked, root5Node1Step3Chunk5_3_checked, root5Node1Step3Chunk5_4_checked, root5Node1Step3Chunk5_5_checked, root5Node1Step3Chunk6_0_checked, root5Node1Step3Chunk6_1_checked, root5Node1Step3Chunk6_2_checked, root5Node1Step3Chunk6_3_checked, root5Node1Step3Chunk6_4_checked, root5Node1Step3Chunk6_5_checked, root5Node1Step3Chunk7_0_checked, root5Node1Step3Chunk7_1_checked, root5Node1Step3Chunk7_2_checked, root5Node1Step3Chunk7_3_checked, root5Node1Step3Chunk7_4_checked, root5Node1Step3Chunk7_5_checked, root5Node1Step3Chunk8_0_checked, root5Node1Step3Chunk8_1_checked, root5Node1Step3Chunk8_2_checked, root5Node1Step3Chunk8_3_checked, root5Node1Step3Chunk8_4_checked, root5Node1Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node1Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,0),(6,0)]
  | 1 => [(1,1),(7,1)]
  | 2 => [(4,1),(5,1),(7,5),(8,1)]
  | 3 => [(0,1),(0,2),(6,0),(6,5)]
  | 4 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 5 => [(1,2),(3,2),(5,2),(7,2)]
  | 6 => [(4,0),(8,0)]
  | 7 => [(7,3),(8,3)]
  | 8 => [(5,2),(5,5),(8,2)]
  | 9 => [(1,0),(3,0),(5,0)]
  | 10 => [(2,1),(2,5),(4,5)]
  | 11 => [(0,3),(0,4),(6,1)]
  | 12 => [(5,1),(5,4)]
  | 13 => [(0,1),(1,4)]
  | 14 => [(0,5),(6,2)]
  | 15 => [(4,4),(8,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2),(7,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(4,3),(5,3),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(1,0),(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node1Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(6,0)]
  | 1 => some [(1,1),(7,1)]
  | 2 => some [(4,1),(5,1),(7,5),(8,1)]
  | 3 => some [(0,1),(0,2),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 5 => some [(1,2),(3,2),(5,2),(7,2)]
  | 6 => some [(4,0),(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2)]
  | 9 => some [(1,0),(3,0),(5,0)]
  | 10 => some [(2,1),(2,5),(4,5)]
  | 11 => some [(0,3),(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(4,3),(5,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node1Domains4_fast_eq : root5Node1Domains4 = expandDomains root5Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node1Domains4 v = expandDomains root5Node1Domains4Fast v from by decide) v
theorem root5Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4_checked :
    checkReplacement table36 root5Node1Domains3 root5Node1Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node1Step4Chunk0_0_checked, root5Node1Step4Chunk0_1_checked, root5Node1Step4Chunk0_2_checked, root5Node1Step4Chunk0_3_checked, root5Node1Step4Chunk0_4_checked, root5Node1Step4Chunk0_5_checked, root5Node1Step4Chunk1_0_checked, root5Node1Step4Chunk1_1_checked, root5Node1Step4Chunk1_2_checked, root5Node1Step4Chunk1_3_checked, root5Node1Step4Chunk1_4_checked, root5Node1Step4Chunk1_5_checked, root5Node1Step4Chunk2_0_checked, root5Node1Step4Chunk2_1_checked, root5Node1Step4Chunk2_2_checked, root5Node1Step4Chunk2_3_checked, root5Node1Step4Chunk2_4_checked, root5Node1Step4Chunk2_5_checked, root5Node1Step4Chunk3_0_checked, root5Node1Step4Chunk3_1_checked, root5Node1Step4Chunk3_2_checked, root5Node1Step4Chunk3_3_checked, root5Node1Step4Chunk3_4_checked, root5Node1Step4Chunk3_5_checked, root5Node1Step4Chunk4_0_checked, root5Node1Step4Chunk4_1_checked, root5Node1Step4Chunk4_2_checked, root5Node1Step4Chunk4_3_checked, root5Node1Step4Chunk4_4_checked, root5Node1Step4Chunk4_5_checked, root5Node1Step4Chunk5_0_checked, root5Node1Step4Chunk5_1_checked, root5Node1Step4Chunk5_2_checked, root5Node1Step4Chunk5_3_checked, root5Node1Step4Chunk5_4_checked, root5Node1Step4Chunk5_5_checked, root5Node1Step4Chunk6_0_checked, root5Node1Step4Chunk6_1_checked, root5Node1Step4Chunk6_2_checked, root5Node1Step4Chunk6_3_checked, root5Node1Step4Chunk6_4_checked, root5Node1Step4Chunk6_5_checked, root5Node1Step4Chunk7_0_checked, root5Node1Step4Chunk7_1_checked, root5Node1Step4Chunk7_2_checked, root5Node1Step4Chunk7_3_checked, root5Node1Step4Chunk7_4_checked, root5Node1Step4Chunk7_5_checked, root5Node1Step4Chunk8_0_checked, root5Node1Step4Chunk8_1_checked, root5Node1Step4Chunk8_2_checked, root5Node1Step4Chunk8_3_checked, root5Node1Step4Chunk8_4_checked, root5Node1Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node2Domains0 : Domains 61 State := restrict root5Node1Domains4 1 (1,1)
def root5Node2Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(6,0)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1),(5,1),(7,5),(8,1)]
  | 3 => some [(0,1),(0,2),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 5 => some [(1,2),(3,2),(5,2),(7,2)]
  | 6 => some [(4,0),(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2)]
  | 9 => some [(1,0),(3,0),(5,0)]
  | 10 => some [(2,1),(2,5),(4,5)]
  | 11 => some [(0,3),(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(4,3),(5,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node2Domains0_fast_eq : root5Node2Domains0 = expandDomains root5Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node2Domains0 v = expandDomains root5Node2Domains0Fast v from by decide) v
def root5Node2Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1),(5,1),(8,1)]
  | 3 => [(0,1),(0,2),(6,5)]
  | 4 => [(0,4),(1,1),(6,2)]
  | 5 => [(1,2),(3,2),(5,2)]
  | 6 => [(4,0),(8,0)]
  | 7 => [(7,3),(8,3)]
  | 8 => [(5,2),(5,5)]
  | 9 => [(1,0),(3,0),(5,0)]
  | 10 => [(2,1),(2,5),(4,5)]
  | 11 => [(0,3),(0,4),(6,1)]
  | 12 => [(5,1),(5,4)]
  | 13 => [(0,1),(1,4)]
  | 14 => [(0,5),(6,2)]
  | 15 => [(4,4),(8,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2),(7,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(4,3),(5,3),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(1,0),(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node2Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1),(5,1),(8,1)]
  | 3 => some [(0,1),(0,2),(6,5)]
  | 4 => some [(0,4),(1,1),(6,2)]
  | 5 => some [(1,2),(3,2),(5,2)]
  | 6 => some [(4,0),(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5)]
  | 9 => some [(1,0),(3,0),(5,0)]
  | 10 => some [(2,1),(2,5),(4,5)]
  | 11 => some [(0,3),(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(4,3),(5,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node2Domains1_fast_eq : root5Node2Domains1 = expandDomains root5Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node2Domains1 v = expandDomains root5Node2Domains1Fast v from by decide) v
theorem root5Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root5Node2Domains0 root5Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains0 root5Node2Domains1
    root5Node2Domains0Fast root5Node2Domains1Fast
    root5Node2Domains0_fast_eq root5Node2Domains1_fast_eq (by decide)
theorem root5Node2Step1_checked :
    checkReplacement table1 root5Node2Domains0 root5Node2Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node2Step1Chunk0_0_checked, root5Node2Step1Chunk0_1_checked, root5Node2Step1Chunk0_2_checked, root5Node2Step1Chunk0_3_checked, root5Node2Step1Chunk0_4_checked, root5Node2Step1Chunk0_5_checked, root5Node2Step1Chunk1_0_checked, root5Node2Step1Chunk1_1_checked, root5Node2Step1Chunk1_2_checked, root5Node2Step1Chunk1_3_checked, root5Node2Step1Chunk1_4_checked, root5Node2Step1Chunk1_5_checked, root5Node2Step1Chunk2_0_checked, root5Node2Step1Chunk2_1_checked, root5Node2Step1Chunk2_2_checked, root5Node2Step1Chunk2_3_checked, root5Node2Step1Chunk2_4_checked, root5Node2Step1Chunk2_5_checked, root5Node2Step1Chunk3_0_checked, root5Node2Step1Chunk3_1_checked, root5Node2Step1Chunk3_2_checked, root5Node2Step1Chunk3_3_checked, root5Node2Step1Chunk3_4_checked, root5Node2Step1Chunk3_5_checked, root5Node2Step1Chunk4_0_checked, root5Node2Step1Chunk4_1_checked, root5Node2Step1Chunk4_2_checked, root5Node2Step1Chunk4_3_checked, root5Node2Step1Chunk4_4_checked, root5Node2Step1Chunk4_5_checked, root5Node2Step1Chunk5_0_checked, root5Node2Step1Chunk5_1_checked, root5Node2Step1Chunk5_2_checked, root5Node2Step1Chunk5_3_checked, root5Node2Step1Chunk5_4_checked, root5Node2Step1Chunk5_5_checked, root5Node2Step1Chunk6_0_checked, root5Node2Step1Chunk6_1_checked, root5Node2Step1Chunk6_2_checked, root5Node2Step1Chunk6_3_checked, root5Node2Step1Chunk6_4_checked, root5Node2Step1Chunk6_5_checked, root5Node2Step1Chunk7_0_checked, root5Node2Step1Chunk7_1_checked, root5Node2Step1Chunk7_2_checked, root5Node2Step1Chunk7_3_checked, root5Node2Step1Chunk7_4_checked, root5Node2Step1Chunk7_5_checked, root5Node2Step1Chunk8_0_checked, root5Node2Step1Chunk8_1_checked, root5Node2Step1Chunk8_2_checked, root5Node2Step1Chunk8_3_checked, root5Node2Step1Chunk8_4_checked, root5Node2Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node2Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1),(5,1),(8,1)]
  | 3 => [(0,1),(0,2),(6,5)]
  | 4 => [(0,4),(1,1),(6,2)]
  | 5 => [(1,2),(3,2),(5,2)]
  | 6 => [(4,0),(8,0)]
  | 7 => [(7,3),(8,3)]
  | 8 => [(5,2),(5,5)]
  | 9 => [(1,0),(3,0),(5,0)]
  | 10 => [(2,1),(2,5),(4,5)]
  | 11 => [(0,3),(0,4),(6,1)]
  | 12 => [(5,1),(5,4)]
  | 13 => [(0,1),(1,4)]
  | 14 => [(0,5),(6,2)]
  | 15 => [(4,4),(8,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2),(7,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(4,3),(5,3),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(1,0),(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(8,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,0)]
  | 54 => [(7,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(3,1)]
  | 59 => [(0,1)]
  | _ => [(6,2)]
def root5Node2Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1),(5,1),(8,1)]
  | 3 => some [(0,1),(0,2),(6,5)]
  | 4 => some [(0,4),(1,1),(6,2)]
  | 5 => some [(1,2),(3,2),(5,2)]
  | 6 => some [(4,0),(8,0)]
  | 7 => some [(7,3),(8,3)]
  | 8 => some [(5,2),(5,5)]
  | 9 => some [(1,0),(3,0),(5,0)]
  | 10 => some [(2,1),(2,5),(4,5)]
  | 11 => some [(0,3),(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(0,1),(1,4)]
  | 14 => some [(0,5),(6,2)]
  | 15 => some [(4,4),(8,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(7,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(4,3),(5,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(1,0),(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(8,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,0)]
  | 54 => some [(7,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(3,1)]
  | 59 => some [(0,1)]
  | _ => some [(6,2)]
theorem root5Node2Domains2_fast_eq : root5Node2Domains2 = expandDomains root5Node2Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node2Domains2 v = expandDomains root5Node2Domains2Fast v from by decide) v
theorem root5Node2Step2Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root5Node2Domains1 root5Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node2Domains1 root5Node2Domains2
    root5Node2Domains1Fast root5Node2Domains2Fast
    root5Node2Domains1_fast_eq root5Node2Domains2_fast_eq (by decide)
theorem root5Node2Step2_checked :
    checkReplacement table4 root5Node2Domains1 root5Node2Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node2Step2Chunk0_0_checked, root5Node2Step2Chunk0_1_checked, root5Node2Step2Chunk0_2_checked, root5Node2Step2Chunk0_3_checked, root5Node2Step2Chunk0_4_checked, root5Node2Step2Chunk0_5_checked, root5Node2Step2Chunk1_0_checked, root5Node2Step2Chunk1_1_checked, root5Node2Step2Chunk1_2_checked, root5Node2Step2Chunk1_3_checked, root5Node2Step2Chunk1_4_checked, root5Node2Step2Chunk1_5_checked, root5Node2Step2Chunk2_0_checked, root5Node2Step2Chunk2_1_checked, root5Node2Step2Chunk2_2_checked, root5Node2Step2Chunk2_3_checked, root5Node2Step2Chunk2_4_checked, root5Node2Step2Chunk2_5_checked, root5Node2Step2Chunk3_0_checked, root5Node2Step2Chunk3_1_checked, root5Node2Step2Chunk3_2_checked, root5Node2Step2Chunk3_3_checked, root5Node2Step2Chunk3_4_checked, root5Node2Step2Chunk3_5_checked, root5Node2Step2Chunk4_0_checked, root5Node2Step2Chunk4_1_checked, root5Node2Step2Chunk4_2_checked, root5Node2Step2Chunk4_3_checked, root5Node2Step2Chunk4_4_checked, root5Node2Step2Chunk4_5_checked, root5Node2Step2Chunk5_0_checked, root5Node2Step2Chunk5_1_checked, root5Node2Step2Chunk5_2_checked, root5Node2Step2Chunk5_3_checked, root5Node2Step2Chunk5_4_checked, root5Node2Step2Chunk5_5_checked, root5Node2Step2Chunk6_0_checked, root5Node2Step2Chunk6_1_checked, root5Node2Step2Chunk6_2_checked, root5Node2Step2Chunk6_3_checked, root5Node2Step2Chunk6_4_checked, root5Node2Step2Chunk6_5_checked, root5Node2Step2Chunk7_0_checked, root5Node2Step2Chunk7_1_checked, root5Node2Step2Chunk7_2_checked, root5Node2Step2Chunk7_3_checked, root5Node2Step2Chunk7_4_checked, root5Node2Step2Chunk7_5_checked, root5Node2Step2Chunk8_0_checked, root5Node2Step2Chunk8_1_checked, root5Node2Step2Chunk8_2_checked, root5Node2Step2Chunk8_3_checked, root5Node2Step2Chunk8_4_checked, root5Node2Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
