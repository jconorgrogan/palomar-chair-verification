module

public import SpectreFinite.RadiusFourRoot1Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable1
public import SpectreFinite.RadiusFourTable21
public import SpectreFinite.RadiusFourTable31
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node1Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4),(5,4),(7,4)]
  | 1 => [(0,0),(6,3),(6,4)]
  | 2 => [(1,2),(7,2)]
  | 3 => [(7,4)]
  | 4 => [(0,5),(1,2),(6,3)]
  | 5 => [(2,1),(2,3),(4,3)]
  | 6 => [(0,2),(1,5),(7,5)]
  | 7 => [(0,3),(1,1),(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(0,0),(1,4),(6,4),(7,4)]
  | 12 => [(0,5),(1,2),(3,2),(6,3)]
  | 13 => [(2,0),(2,2),(4,0)]
  | 14 => [(3,3),(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3),(8,3)]
  | 18 => [(1,5),(4,1),(7,5)]
  | 19 => [(0,2),(0,3),(6,0),(6,1)]
  | 20 => [(1,1),(3,1),(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => [(4,2),(5,2),(7,0),(8,2)]
  | 28 => [(5,0),(5,3),(8,3)]
  | 29 => [(4,5),(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(5,1),(7,1),(8,1)]
  | 35 => [(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => [(7,4),(8,4)]
  | 37 => [(0,0),(1,3),(6,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,0),(8,3)]
  | 43 => [(4,1),(7,1),(7,5),(8,1)]
  | 44 => [(0,2),(1,5),(6,5)]
  | 45 => [(0,4),(1,1),(6,1)]
  | 46 => [(5,1),(5,4)]
  | 47 => [(0,0),(0,1),(6,4)]
  | 48 => [(1,2),(6,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(4,5),(5,2),(5,5),(8,2),(8,5)]
  | 51 => [(5,0),(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => [(0,3),(1,0),(6,1)]
  | 55 => [(2,1),(4,1),(7,1),(8,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(0,0),(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3),(7,2)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(7,4),(8,2)]
  | _ => [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(6,3),(7,3),(8,0)]
def root1Node1Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(6,3),(6,4)]
  | 2 => some [(1,2),(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(0,5),(1,2),(6,3)]
  | 5 => some [(2,1),(2,3),(4,3)]
  | 6 => some [(0,2),(1,5),(7,5)]
  | 7 => some [(0,3),(1,1),(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,0),(1,4),(6,4),(7,4)]
  | 12 => some [(0,5),(1,2),(3,2),(6,3)]
  | 13 => some [(2,0),(2,2),(4,0)]
  | 14 => some [(3,3),(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(1,5),(4,1),(7,5)]
  | 19 => some [(0,2),(0,3),(6,0),(6,1)]
  | 20 => some [(1,1),(3,1),(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => some [(4,2),(5,2),(7,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0),(8,3)]
  | 43 => some [(4,1),(7,1),(7,5),(8,1)]
  | 44 => some [(0,2),(1,5),(6,5)]
  | 45 => some [(0,4),(1,1),(6,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,2),(5,5),(8,2),(8,5)]
  | 51 => some [(5,0),(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(7,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(0,0),(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3),(7,2)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(7,4),(8,2)]
  | _ => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(6,3),(7,3),(8,0)]
theorem root1Node1Domains2_fast_eq : root1Node1Domains2 = expandDomains root1Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node1Domains2 v = expandDomains root1Node1Domains2Fast v from by decide) v
theorem root1Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_0⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_1⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_2⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_3⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_4⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_5⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_0⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_1⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_2⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_3⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_4⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_5⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_0⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_1⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_2⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_3⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_4⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_5⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_0⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_1⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_2⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_3⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_4⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_5⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_0⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_1⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_2⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_3⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_4⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_5⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_0⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_1⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_2⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_3⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_4⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_5⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_0⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_1⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_2⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_3⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_4⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_5⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_0⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_1⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_2⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_3⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_4⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_5⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_0⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_1⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_2⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_3⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_4⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_5⟩
      root1Node1Domains1 root1Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains1 root1Node1Domains2
    root1Node1Domains1Fast root1Node1Domains2Fast
    root1Node1Domains1_fast_eq root1Node1Domains2_fast_eq (by decide)
theorem root1Node1Step2_checked :
    checkReplacement table31 root1Node1Domains1 root1Node1Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node1Step2Chunk0_0_checked, root1Node1Step2Chunk0_1_checked, root1Node1Step2Chunk0_2_checked, root1Node1Step2Chunk0_3_checked, root1Node1Step2Chunk0_4_checked, root1Node1Step2Chunk0_5_checked, root1Node1Step2Chunk1_0_checked, root1Node1Step2Chunk1_1_checked, root1Node1Step2Chunk1_2_checked, root1Node1Step2Chunk1_3_checked, root1Node1Step2Chunk1_4_checked, root1Node1Step2Chunk1_5_checked, root1Node1Step2Chunk2_0_checked, root1Node1Step2Chunk2_1_checked, root1Node1Step2Chunk2_2_checked, root1Node1Step2Chunk2_3_checked, root1Node1Step2Chunk2_4_checked, root1Node1Step2Chunk2_5_checked, root1Node1Step2Chunk3_0_checked, root1Node1Step2Chunk3_1_checked, root1Node1Step2Chunk3_2_checked, root1Node1Step2Chunk3_3_checked, root1Node1Step2Chunk3_4_checked, root1Node1Step2Chunk3_5_checked, root1Node1Step2Chunk4_0_checked, root1Node1Step2Chunk4_1_checked, root1Node1Step2Chunk4_2_checked, root1Node1Step2Chunk4_3_checked, root1Node1Step2Chunk4_4_checked, root1Node1Step2Chunk4_5_checked, root1Node1Step2Chunk5_0_checked, root1Node1Step2Chunk5_1_checked, root1Node1Step2Chunk5_2_checked, root1Node1Step2Chunk5_3_checked, root1Node1Step2Chunk5_4_checked, root1Node1Step2Chunk5_5_checked, root1Node1Step2Chunk6_0_checked, root1Node1Step2Chunk6_1_checked, root1Node1Step2Chunk6_2_checked, root1Node1Step2Chunk6_3_checked, root1Node1Step2Chunk6_4_checked, root1Node1Step2Chunk6_5_checked, root1Node1Step2Chunk7_0_checked, root1Node1Step2Chunk7_1_checked, root1Node1Step2Chunk7_2_checked, root1Node1Step2Chunk7_3_checked, root1Node1Step2Chunk7_4_checked, root1Node1Step2Chunk7_5_checked, root1Node1Step2Chunk8_0_checked, root1Node1Step2Chunk8_1_checked, root1Node1Step2Chunk8_2_checked, root1Node1Step2Chunk8_3_checked, root1Node1Step2Chunk8_4_checked, root1Node1Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node1Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4),(5,4),(7,4)]
  | 1 => [(0,0),(6,3),(6,4)]
  | 2 => [(1,2),(7,2)]
  | 3 => [(7,4)]
  | 4 => [(0,5),(1,2),(6,3)]
  | 5 => [(2,1),(2,3),(4,3)]
  | 6 => [(0,2),(1,5),(7,5)]
  | 7 => [(0,3),(1,1),(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(0,0),(1,4),(6,4),(7,4)]
  | 12 => [(0,5),(1,2),(3,2),(6,3)]
  | 13 => [(2,0),(2,2),(4,0)]
  | 14 => [(3,3),(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3),(8,3)]
  | 18 => [(1,5),(4,1),(7,5)]
  | 19 => [(0,2),(0,3),(6,0),(6,1)]
  | 20 => [(1,1),(3,1),(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,2),(5,2),(7,0),(8,2)]
  | 28 => [(5,0),(5,3),(8,3)]
  | 29 => [(4,5),(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(5,1),(7,1),(8,1)]
  | 35 => [(1,2),(6,2),(7,2)]
  | 36 => [(7,4),(8,4)]
  | 37 => [(0,0),(1,3),(6,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,0),(8,3)]
  | 43 => [(4,1),(7,1),(8,1)]
  | 44 => [(0,2),(1,5),(6,5)]
  | 45 => [(0,4),(1,1),(6,1)]
  | 46 => [(5,1),(5,4)]
  | 47 => [(0,0),(0,1),(6,4)]
  | 48 => [(1,2),(6,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(4,5),(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => [(0,3),(1,0),(6,1)]
  | 55 => [(2,1),(4,1),(7,1),(8,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(7,4),(8,2)]
  | _ => [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(6,3),(7,3),(8,0)]
def root1Node1Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(6,3),(6,4)]
  | 2 => some [(1,2),(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(0,5),(1,2),(6,3)]
  | 5 => some [(2,1),(2,3),(4,3)]
  | 6 => some [(0,2),(1,5),(7,5)]
  | 7 => some [(0,3),(1,1),(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,0),(1,4),(6,4),(7,4)]
  | 12 => some [(0,5),(1,2),(3,2),(6,3)]
  | 13 => some [(2,0),(2,2),(4,0)]
  | 14 => some [(3,3),(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(1,5),(4,1),(7,5)]
  | 19 => some [(0,2),(0,3),(6,0),(6,1)]
  | 20 => some [(1,1),(3,1),(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(5,2),(7,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(6,2),(7,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0),(8,3)]
  | 43 => some [(4,1),(7,1),(8,1)]
  | 44 => some [(0,2),(1,5),(6,5)]
  | 45 => some [(0,4),(1,1),(6,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(7,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(7,4),(8,2)]
  | _ => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(6,3),(7,3),(8,0)]
theorem root1Node1Domains3_fast_eq : root1Node1Domains3 = expandDomains root1Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node1Domains3 v = expandDomains root1Node1Domains3Fast v from by decide) v
theorem root1Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root1Node1Domains2 root1Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains2 root1Node1Domains3
    root1Node1Domains2Fast root1Node1Domains3Fast
    root1Node1Domains2_fast_eq root1Node1Domains3_fast_eq (by decide)
theorem root1Node1Step3_checked :
    checkReplacement table37 root1Node1Domains2 root1Node1Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node1Step3Chunk0_0_checked, root1Node1Step3Chunk0_1_checked, root1Node1Step3Chunk0_2_checked, root1Node1Step3Chunk0_3_checked, root1Node1Step3Chunk0_4_checked, root1Node1Step3Chunk0_5_checked, root1Node1Step3Chunk1_0_checked, root1Node1Step3Chunk1_1_checked, root1Node1Step3Chunk1_2_checked, root1Node1Step3Chunk1_3_checked, root1Node1Step3Chunk1_4_checked, root1Node1Step3Chunk1_5_checked, root1Node1Step3Chunk2_0_checked, root1Node1Step3Chunk2_1_checked, root1Node1Step3Chunk2_2_checked, root1Node1Step3Chunk2_3_checked, root1Node1Step3Chunk2_4_checked, root1Node1Step3Chunk2_5_checked, root1Node1Step3Chunk3_0_checked, root1Node1Step3Chunk3_1_checked, root1Node1Step3Chunk3_2_checked, root1Node1Step3Chunk3_3_checked, root1Node1Step3Chunk3_4_checked, root1Node1Step3Chunk3_5_checked, root1Node1Step3Chunk4_0_checked, root1Node1Step3Chunk4_1_checked, root1Node1Step3Chunk4_2_checked, root1Node1Step3Chunk4_3_checked, root1Node1Step3Chunk4_4_checked, root1Node1Step3Chunk4_5_checked, root1Node1Step3Chunk5_0_checked, root1Node1Step3Chunk5_1_checked, root1Node1Step3Chunk5_2_checked, root1Node1Step3Chunk5_3_checked, root1Node1Step3Chunk5_4_checked, root1Node1Step3Chunk5_5_checked, root1Node1Step3Chunk6_0_checked, root1Node1Step3Chunk6_1_checked, root1Node1Step3Chunk6_2_checked, root1Node1Step3Chunk6_3_checked, root1Node1Step3Chunk6_4_checked, root1Node1Step3Chunk6_5_checked, root1Node1Step3Chunk7_0_checked, root1Node1Step3Chunk7_1_checked, root1Node1Step3Chunk7_2_checked, root1Node1Step3Chunk7_3_checked, root1Node1Step3Chunk7_4_checked, root1Node1Step3Chunk7_5_checked, root1Node1Step3Chunk8_0_checked, root1Node1Step3Chunk8_1_checked, root1Node1Step3Chunk8_2_checked, root1Node1Step3Chunk8_3_checked, root1Node1Step3Chunk8_4_checked, root1Node1Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node1Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4),(5,4),(7,4)]
  | 1 => [(0,0),(6,3),(6,4)]
  | 2 => [(1,2),(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,1),(2,3),(4,3)]
  | 6 => [(0,2),(1,5),(7,5)]
  | 7 => [(0,3),(1,1),(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(0,0),(1,4),(6,4),(7,4)]
  | 12 => [(0,5),(1,2),(3,2),(6,3)]
  | 13 => [(2,0),(2,2),(4,0)]
  | 14 => [(3,3),(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3),(8,3)]
  | 18 => [(1,5),(4,1),(7,5)]
  | 19 => [(0,2),(0,3),(6,0),(6,1)]
  | 20 => [(1,1),(3,1),(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,2),(5,2),(7,0),(8,2)]
  | 28 => [(5,0),(5,3),(8,3)]
  | 29 => [(4,5),(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(5,1),(7,1),(8,1)]
  | 35 => [(1,2),(6,2),(7,2)]
  | 36 => [(7,4),(8,4)]
  | 37 => [(0,0),(1,3),(6,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,0),(8,3)]
  | 43 => [(4,1),(7,1),(8,1)]
  | 44 => [(0,2),(1,5),(6,5)]
  | 45 => [(0,4),(1,1),(6,1)]
  | 46 => [(5,1),(5,4)]
  | 47 => [(0,0),(0,1),(6,4)]
  | 48 => [(1,2),(6,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(4,5),(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => [(0,3),(1,0),(6,1)]
  | 55 => [(2,1),(4,1),(7,1),(8,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(7,4),(8,2)]
  | _ => [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(6,3),(7,3),(8,0)]
def root1Node1Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(6,3),(6,4)]
  | 2 => some [(1,2),(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,1),(2,3),(4,3)]
  | 6 => some [(0,2),(1,5),(7,5)]
  | 7 => some [(0,3),(1,1),(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,0),(1,4),(6,4),(7,4)]
  | 12 => some [(0,5),(1,2),(3,2),(6,3)]
  | 13 => some [(2,0),(2,2),(4,0)]
  | 14 => some [(3,3),(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(1,5),(4,1),(7,5)]
  | 19 => some [(0,2),(0,3),(6,0),(6,1)]
  | 20 => some [(1,1),(3,1),(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(5,2),(7,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(6,2),(7,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0),(8,3)]
  | 43 => some [(4,1),(7,1),(8,1)]
  | 44 => some [(0,2),(1,5),(6,5)]
  | 45 => some [(0,4),(1,1),(6,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(7,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(7,4),(8,2)]
  | _ => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(6,3),(7,3),(8,0)]
theorem root1Node1Domains4_fast_eq : root1Node1Domains4 = expandDomains root1Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node1Domains4 v = expandDomains root1Node1Domains4Fast v from by decide) v
theorem root1Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root1Node1Domains3 root1Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains3 root1Node1Domains4
    root1Node1Domains3Fast root1Node1Domains4Fast
    root1Node1Domains3_fast_eq root1Node1Domains4_fast_eq (by decide)
theorem root1Node1Step4_checked :
    checkReplacement table1 root1Node1Domains3 root1Node1Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node1Step4Chunk0_0_checked, root1Node1Step4Chunk0_1_checked, root1Node1Step4Chunk0_2_checked, root1Node1Step4Chunk0_3_checked, root1Node1Step4Chunk0_4_checked, root1Node1Step4Chunk0_5_checked, root1Node1Step4Chunk1_0_checked, root1Node1Step4Chunk1_1_checked, root1Node1Step4Chunk1_2_checked, root1Node1Step4Chunk1_3_checked, root1Node1Step4Chunk1_4_checked, root1Node1Step4Chunk1_5_checked, root1Node1Step4Chunk2_0_checked, root1Node1Step4Chunk2_1_checked, root1Node1Step4Chunk2_2_checked, root1Node1Step4Chunk2_3_checked, root1Node1Step4Chunk2_4_checked, root1Node1Step4Chunk2_5_checked, root1Node1Step4Chunk3_0_checked, root1Node1Step4Chunk3_1_checked, root1Node1Step4Chunk3_2_checked, root1Node1Step4Chunk3_3_checked, root1Node1Step4Chunk3_4_checked, root1Node1Step4Chunk3_5_checked, root1Node1Step4Chunk4_0_checked, root1Node1Step4Chunk4_1_checked, root1Node1Step4Chunk4_2_checked, root1Node1Step4Chunk4_3_checked, root1Node1Step4Chunk4_4_checked, root1Node1Step4Chunk4_5_checked, root1Node1Step4Chunk5_0_checked, root1Node1Step4Chunk5_1_checked, root1Node1Step4Chunk5_2_checked, root1Node1Step4Chunk5_3_checked, root1Node1Step4Chunk5_4_checked, root1Node1Step4Chunk5_5_checked, root1Node1Step4Chunk6_0_checked, root1Node1Step4Chunk6_1_checked, root1Node1Step4Chunk6_2_checked, root1Node1Step4Chunk6_3_checked, root1Node1Step4Chunk6_4_checked, root1Node1Step4Chunk6_5_checked, root1Node1Step4Chunk7_0_checked, root1Node1Step4Chunk7_1_checked, root1Node1Step4Chunk7_2_checked, root1Node1Step4Chunk7_3_checked, root1Node1Step4Chunk7_4_checked, root1Node1Step4Chunk7_5_checked, root1Node1Step4Chunk8_0_checked, root1Node1Step4Chunk8_1_checked, root1Node1Step4Chunk8_2_checked, root1Node1Step4Chunk8_3_checked, root1Node1Step4Chunk8_4_checked, root1Node1Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node1Domains5 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4),(5,4),(7,4)]
  | 1 => [(0,0),(6,3),(6,4)]
  | 2 => [(1,2),(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,1),(2,3),(4,3)]
  | 6 => [(0,2),(1,5),(7,5)]
  | 7 => [(0,3),(1,1),(6,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(0,0),(1,4),(6,4),(7,4)]
  | 12 => [(0,5),(1,2),(3,2),(6,3)]
  | 13 => [(2,0),(2,2),(4,0)]
  | 14 => [(3,3),(7,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3),(8,3)]
  | 18 => [(1,5),(4,1),(7,5)]
  | 19 => [(0,2),(0,3),(6,0),(6,1)]
  | 20 => [(1,1),(3,1),(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(4,2),(5,2),(7,0),(8,2)]
  | 28 => [(5,0),(5,3),(8,3)]
  | 29 => [(4,5),(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(5,1),(7,1),(8,1)]
  | 35 => [(1,2),(6,2),(7,2)]
  | 36 => [(7,4),(8,4)]
  | 37 => [(0,0),(1,3),(6,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,0),(8,3)]
  | 43 => [(4,1),(7,1),(8,1)]
  | 44 => [(0,2),(1,5),(6,5)]
  | 45 => [(0,4),(1,1),(6,1)]
  | 46 => [(5,1),(5,4)]
  | 47 => [(0,0),(0,1),(6,4)]
  | 48 => [(1,2),(6,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(4,5),(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => [(0,3),(1,0),(6,1)]
  | 55 => [(2,1),(4,1),(7,1),(8,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | _ => [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
def root1Node1Domains5Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(6,3),(6,4)]
  | 2 => some [(1,2),(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,1),(2,3),(4,3)]
  | 6 => some [(0,2),(1,5),(7,5)]
  | 7 => some [(0,3),(1,1),(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,0),(1,4),(6,4),(7,4)]
  | 12 => some [(0,5),(1,2),(3,2),(6,3)]
  | 13 => some [(2,0),(2,2),(4,0)]
  | 14 => some [(3,3),(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(1,5),(4,1),(7,5)]
  | 19 => some [(0,2),(0,3),(6,0),(6,1)]
  | 20 => some [(1,1),(3,1),(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(5,2),(7,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(6,2),(7,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0),(8,3)]
  | 43 => some [(4,1),(7,1),(8,1)]
  | 44 => some [(0,2),(1,5),(6,5)]
  | 45 => some [(0,4),(1,1),(6,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(7,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
theorem root1Node1Domains5_fast_eq : root1Node1Domains5 = expandDomains root1Node1Domains5Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node1Domains5 v = expandDomains root1Node1Domains5Fast v from by decide) v
theorem root1Node1Step5Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root1Node1Domains4 root1Node1Domains5 = true := by
  exact checkNarrowing_of_fast _ root1Node1Domains4 root1Node1Domains5
    root1Node1Domains4Fast root1Node1Domains5Fast
    root1Node1Domains4_fast_eq root1Node1Domains5_fast_eq (by decide)
theorem root1Node1Step5_checked :
    checkReplacement table39 root1Node1Domains4 root1Node1Domains5 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node1Step5Chunk0_0_checked, root1Node1Step5Chunk0_1_checked, root1Node1Step5Chunk0_2_checked, root1Node1Step5Chunk0_3_checked, root1Node1Step5Chunk0_4_checked, root1Node1Step5Chunk0_5_checked, root1Node1Step5Chunk1_0_checked, root1Node1Step5Chunk1_1_checked, root1Node1Step5Chunk1_2_checked, root1Node1Step5Chunk1_3_checked, root1Node1Step5Chunk1_4_checked, root1Node1Step5Chunk1_5_checked, root1Node1Step5Chunk2_0_checked, root1Node1Step5Chunk2_1_checked, root1Node1Step5Chunk2_2_checked, root1Node1Step5Chunk2_3_checked, root1Node1Step5Chunk2_4_checked, root1Node1Step5Chunk2_5_checked, root1Node1Step5Chunk3_0_checked, root1Node1Step5Chunk3_1_checked, root1Node1Step5Chunk3_2_checked, root1Node1Step5Chunk3_3_checked, root1Node1Step5Chunk3_4_checked, root1Node1Step5Chunk3_5_checked, root1Node1Step5Chunk4_0_checked, root1Node1Step5Chunk4_1_checked, root1Node1Step5Chunk4_2_checked, root1Node1Step5Chunk4_3_checked, root1Node1Step5Chunk4_4_checked, root1Node1Step5Chunk4_5_checked, root1Node1Step5Chunk5_0_checked, root1Node1Step5Chunk5_1_checked, root1Node1Step5Chunk5_2_checked, root1Node1Step5Chunk5_3_checked, root1Node1Step5Chunk5_4_checked, root1Node1Step5Chunk5_5_checked, root1Node1Step5Chunk6_0_checked, root1Node1Step5Chunk6_1_checked, root1Node1Step5Chunk6_2_checked, root1Node1Step5Chunk6_3_checked, root1Node1Step5Chunk6_4_checked, root1Node1Step5Chunk6_5_checked, root1Node1Step5Chunk7_0_checked, root1Node1Step5Chunk7_1_checked, root1Node1Step5Chunk7_2_checked, root1Node1Step5Chunk7_3_checked, root1Node1Step5Chunk7_4_checked, root1Node1Step5Chunk7_5_checked, root1Node1Step5Chunk8_0_checked, root1Node1Step5Chunk8_1_checked, root1Node1Step5Chunk8_2_checked, root1Node1Step5Chunk8_3_checked, root1Node1Step5Chunk8_4_checked, root1Node1Step5Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node2Domains0 : Domains 61 State := restrict root1Node1Domains5 2 (1,2)
def root1Node2Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4),(5,4),(7,4)]
  | 1 => some [(0,0),(6,3),(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,1),(2,3),(4,3)]
  | 6 => some [(0,2),(1,5),(7,5)]
  | 7 => some [(0,3),(1,1),(6,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(0,0),(1,4),(6,4),(7,4)]
  | 12 => some [(0,5),(1,2),(3,2),(6,3)]
  | 13 => some [(2,0),(2,2),(4,0)]
  | 14 => some [(3,3),(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(1,5),(4,1),(7,5)]
  | 19 => some [(0,2),(0,3),(6,0),(6,1)]
  | 20 => some [(1,1),(3,1),(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(4,2),(5,2),(7,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(6,2),(7,2)]
  | 36 => some [(7,4),(8,4)]
  | 37 => some [(0,0),(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0),(8,3)]
  | 43 => some [(4,1),(7,1),(8,1)]
  | 44 => some [(0,2),(1,5),(6,5)]
  | 45 => some [(0,4),(1,1),(6,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(7,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
theorem root1Node2Domains0_fast_eq : root1Node2Domains0 = expandDomains root1Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node2Domains0 v = expandDomains root1Node2Domains0Fast v from by decide) v
def root1Node2Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(7,4)]
  | 12 => [(6,3)]
  | 13 => [(2,2)]
  | 14 => [(3,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(4,5),(7,3),(8,3)]
  | 18 => [(4,1)]
  | 19 => [(0,2)]
  | 20 => [(1,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(4,5),(7,3)]
  | 27 => [(5,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(5,1),(7,1),(8,1)]
  | 35 => [(1,2),(6,2),(7,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,0),(8,3)]
  | 43 => [(4,1),(7,1),(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(1,2),(6,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(4,5),(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => [(0,3),(1,0),(6,1)]
  | 55 => [(2,1),(4,1),(7,1),(8,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(1,3),(6,3)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | _ => [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
def root1Node2Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(7,4)]
  | 12 => some [(6,3)]
  | 13 => some [(2,2)]
  | 14 => some [(3,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(4,5),(7,3),(8,3)]
  | 18 => some [(4,1)]
  | 19 => some [(0,2)]
  | 20 => some [(1,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(4,5),(7,3)]
  | 27 => some [(5,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(5,1),(7,1),(8,1)]
  | 35 => some [(1,2),(6,2),(7,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,0),(8,3)]
  | 43 => some [(4,1),(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(4,5),(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1),(7,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | _ => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
theorem root1Node2Domains1_fast_eq : root1Node2Domains1 = expandDomains root1Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node2Domains1 v = expandDomains root1Node2Domains1Fast v from by decide) v
theorem root1Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root1Node2Domains0 root1Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node2Domains0 root1Node2Domains1
    root1Node2Domains0Fast root1Node2Domains1Fast
    root1Node2Domains0_fast_eq root1Node2Domains1_fast_eq (by decide)
theorem root1Node2Step1_checked :
    checkReplacement table21 root1Node2Domains0 root1Node2Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node2Step1Chunk0_0_checked, root1Node2Step1Chunk0_1_checked, root1Node2Step1Chunk0_2_checked, root1Node2Step1Chunk0_3_checked, root1Node2Step1Chunk0_4_checked, root1Node2Step1Chunk0_5_checked, root1Node2Step1Chunk1_0_checked, root1Node2Step1Chunk1_1_checked, root1Node2Step1Chunk1_2_checked, root1Node2Step1Chunk1_3_checked, root1Node2Step1Chunk1_4_checked, root1Node2Step1Chunk1_5_checked, root1Node2Step1Chunk2_0_checked, root1Node2Step1Chunk2_1_checked, root1Node2Step1Chunk2_2_checked, root1Node2Step1Chunk2_3_checked, root1Node2Step1Chunk2_4_checked, root1Node2Step1Chunk2_5_checked, root1Node2Step1Chunk3_0_checked, root1Node2Step1Chunk3_1_checked, root1Node2Step1Chunk3_2_checked, root1Node2Step1Chunk3_3_checked, root1Node2Step1Chunk3_4_checked, root1Node2Step1Chunk3_5_checked, root1Node2Step1Chunk4_0_checked, root1Node2Step1Chunk4_1_checked, root1Node2Step1Chunk4_2_checked, root1Node2Step1Chunk4_3_checked, root1Node2Step1Chunk4_4_checked, root1Node2Step1Chunk4_5_checked, root1Node2Step1Chunk5_0_checked, root1Node2Step1Chunk5_1_checked, root1Node2Step1Chunk5_2_checked, root1Node2Step1Chunk5_3_checked, root1Node2Step1Chunk5_4_checked, root1Node2Step1Chunk5_5_checked, root1Node2Step1Chunk6_0_checked, root1Node2Step1Chunk6_1_checked, root1Node2Step1Chunk6_2_checked, root1Node2Step1Chunk6_3_checked, root1Node2Step1Chunk6_4_checked, root1Node2Step1Chunk6_5_checked, root1Node2Step1Chunk7_0_checked, root1Node2Step1Chunk7_1_checked, root1Node2Step1Chunk7_2_checked, root1Node2Step1Chunk7_3_checked, root1Node2Step1Chunk7_4_checked, root1Node2Step1Chunk7_5_checked, root1Node2Step1Chunk8_0_checked, root1Node2Step1Chunk8_1_checked, root1Node2Step1Chunk8_2_checked, root1Node2Step1Chunk8_3_checked, root1Node2Step1Chunk8_4_checked, root1Node2Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
