module

public import SpectreFinite.RadiusFourRoot0Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable11
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable46
public import SpectreFinite.RadiusFourTable5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node1Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 11 => [(1,1),(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(4,4),(5,1),(5,4),(7,2),(8,1),(8,4)]
  | 18 => [(7,0),(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(1,0)]
  | 22 => [(2,1)]
  | 23 => [(0,2)]
  | 24 => [(1,1)]
  | 25 => [(4,1),(7,5),(8,5)]
  | 26 => [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(3,2)]
  | 32 => [(4,0)]
  | 33 => [(1,3),(6,3),(7,3)]
  | 34 => [(4,2),(5,2),(7,2),(8,2)]
  | 35 => [(5,5),(7,5),(8,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(0,4),(1,1),(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(5,4),(8,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1),(8,1)]
  | 59 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root0Node1Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(2,1),(2,5),(4,1),(4,5),(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 11 => some [(1,1),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(4,4),(5,1),(5,4),(7,2),(8,1),(8,4)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(2,1)]
  | 23 => some [(0,2)]
  | 24 => some [(1,1)]
  | 25 => some [(4,1),(7,5),(8,5)]
  | 26 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(3,2)]
  | 32 => some [(4,0)]
  | 33 => some [(1,3),(6,3),(7,3)]
  | 34 => some [(4,2),(5,2),(7,2),(8,2)]
  | 35 => some [(5,5),(7,5),(8,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(0,4),(1,1),(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node1Domains2_fast_eq : root0Node1Domains2 = expandDomains root0Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node1Domains2 v = expandDomains root0Node1Domains2Fast v from by decide) v
theorem root0Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root0Node1Domains1 root0Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains1 root0Node1Domains2
    root0Node1Domains1Fast root0Node1Domains2Fast
    root0Node1Domains1_fast_eq root0Node1Domains2_fast_eq (by decide)
theorem root0Node1Step2_checked :
    checkReplacement table46 root0Node1Domains1 root0Node1Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node1Step2Chunk0_0_checked, root0Node1Step2Chunk0_1_checked, root0Node1Step2Chunk0_2_checked, root0Node1Step2Chunk0_3_checked, root0Node1Step2Chunk0_4_checked, root0Node1Step2Chunk0_5_checked, root0Node1Step2Chunk1_0_checked, root0Node1Step2Chunk1_1_checked, root0Node1Step2Chunk1_2_checked, root0Node1Step2Chunk1_3_checked, root0Node1Step2Chunk1_4_checked, root0Node1Step2Chunk1_5_checked, root0Node1Step2Chunk2_0_checked, root0Node1Step2Chunk2_1_checked, root0Node1Step2Chunk2_2_checked, root0Node1Step2Chunk2_3_checked, root0Node1Step2Chunk2_4_checked, root0Node1Step2Chunk2_5_checked, root0Node1Step2Chunk3_0_checked, root0Node1Step2Chunk3_1_checked, root0Node1Step2Chunk3_2_checked, root0Node1Step2Chunk3_3_checked, root0Node1Step2Chunk3_4_checked, root0Node1Step2Chunk3_5_checked, root0Node1Step2Chunk4_0_checked, root0Node1Step2Chunk4_1_checked, root0Node1Step2Chunk4_2_checked, root0Node1Step2Chunk4_3_checked, root0Node1Step2Chunk4_4_checked, root0Node1Step2Chunk4_5_checked, root0Node1Step2Chunk5_0_checked, root0Node1Step2Chunk5_1_checked, root0Node1Step2Chunk5_2_checked, root0Node1Step2Chunk5_3_checked, root0Node1Step2Chunk5_4_checked, root0Node1Step2Chunk5_5_checked, root0Node1Step2Chunk6_0_checked, root0Node1Step2Chunk6_1_checked, root0Node1Step2Chunk6_2_checked, root0Node1Step2Chunk6_3_checked, root0Node1Step2Chunk6_4_checked, root0Node1Step2Chunk6_5_checked, root0Node1Step2Chunk7_0_checked, root0Node1Step2Chunk7_1_checked, root0Node1Step2Chunk7_2_checked, root0Node1Step2Chunk7_3_checked, root0Node1Step2Chunk7_4_checked, root0Node1Step2Chunk7_5_checked, root0Node1Step2Chunk8_0_checked, root0Node1Step2Chunk8_1_checked, root0Node1Step2Chunk8_2_checked, root0Node1Step2Chunk8_3_checked, root0Node1Step2Chunk8_4_checked, root0Node1Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node1Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(8,5)]
  | 11 => [(1,1),(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(7,2)]
  | 18 => [(7,0),(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(1,0)]
  | 22 => [(2,1)]
  | 23 => [(0,2)]
  | 24 => [(1,1)]
  | 25 => [(4,1)]
  | 26 => [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(3,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(5,2)]
  | 35 => [(5,5),(7,5),(8,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(5,4),(8,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1),(8,1)]
  | 59 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root0Node1Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,1),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(2,1)]
  | 23 => some [(0,2)]
  | 24 => some [(1,1)]
  | 25 => some [(4,1)]
  | 26 => some [(4,4),(5,1),(5,4),(8,1),(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(3,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(5,2)]
  | 35 => some [(5,5),(7,5),(8,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node1Domains3_fast_eq : root0Node1Domains3 = expandDomains root0Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node1Domains3 v = expandDomains root0Node1Domains3Fast v from by decide) v
theorem root0Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root0Node1Domains2 root0Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains2 root0Node1Domains3
    root0Node1Domains2Fast root0Node1Domains3Fast
    root0Node1Domains2_fast_eq root0Node1Domains3_fast_eq (by decide)
theorem root0Node1Step3_checked :
    checkReplacement table16 root0Node1Domains2 root0Node1Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node1Step3Chunk0_0_checked, root0Node1Step3Chunk0_1_checked, root0Node1Step3Chunk0_2_checked, root0Node1Step3Chunk0_3_checked, root0Node1Step3Chunk0_4_checked, root0Node1Step3Chunk0_5_checked, root0Node1Step3Chunk1_0_checked, root0Node1Step3Chunk1_1_checked, root0Node1Step3Chunk1_2_checked, root0Node1Step3Chunk1_3_checked, root0Node1Step3Chunk1_4_checked, root0Node1Step3Chunk1_5_checked, root0Node1Step3Chunk2_0_checked, root0Node1Step3Chunk2_1_checked, root0Node1Step3Chunk2_2_checked, root0Node1Step3Chunk2_3_checked, root0Node1Step3Chunk2_4_checked, root0Node1Step3Chunk2_5_checked, root0Node1Step3Chunk3_0_checked, root0Node1Step3Chunk3_1_checked, root0Node1Step3Chunk3_2_checked, root0Node1Step3Chunk3_3_checked, root0Node1Step3Chunk3_4_checked, root0Node1Step3Chunk3_5_checked, root0Node1Step3Chunk4_0_checked, root0Node1Step3Chunk4_1_checked, root0Node1Step3Chunk4_2_checked, root0Node1Step3Chunk4_3_checked, root0Node1Step3Chunk4_4_checked, root0Node1Step3Chunk4_5_checked, root0Node1Step3Chunk5_0_checked, root0Node1Step3Chunk5_1_checked, root0Node1Step3Chunk5_2_checked, root0Node1Step3Chunk5_3_checked, root0Node1Step3Chunk5_4_checked, root0Node1Step3Chunk5_5_checked, root0Node1Step3Chunk6_0_checked, root0Node1Step3Chunk6_1_checked, root0Node1Step3Chunk6_2_checked, root0Node1Step3Chunk6_3_checked, root0Node1Step3Chunk6_4_checked, root0Node1Step3Chunk6_5_checked, root0Node1Step3Chunk7_0_checked, root0Node1Step3Chunk7_1_checked, root0Node1Step3Chunk7_2_checked, root0Node1Step3Chunk7_3_checked, root0Node1Step3Chunk7_4_checked, root0Node1Step3Chunk7_5_checked, root0Node1Step3Chunk8_0_checked, root0Node1Step3Chunk8_1_checked, root0Node1Step3Chunk8_2_checked, root0Node1Step3Chunk8_3_checked, root0Node1Step3Chunk8_4_checked, root0Node1Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node1Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(8,5)]
  | 11 => [(1,1),(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(7,2)]
  | 18 => [(7,0),(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(1,0)]
  | 22 => [(2,1)]
  | 23 => [(0,2)]
  | 24 => [(1,1)]
  | 25 => [(4,1)]
  | 26 => [(4,4),(5,4),(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(3,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(5,2)]
  | 35 => [(7,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(5,4),(8,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1),(8,1)]
  | 59 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root0Node1Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,1),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(2,1)]
  | 23 => some [(0,2)]
  | 24 => some [(1,1)]
  | 25 => some [(4,1)]
  | 26 => some [(4,4),(5,4),(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(3,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(5,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node1Domains4_fast_eq : root0Node1Domains4 = expandDomains root0Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node1Domains4 v = expandDomains root0Node1Domains4Fast v from by decide) v
theorem root0Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root0Node1Domains3 root0Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node1Domains3 root0Node1Domains4
    root0Node1Domains3Fast root0Node1Domains4Fast
    root0Node1Domains3_fast_eq root0Node1Domains4_fast_eq (by decide)
theorem root0Node1Step4_checked :
    checkReplacement table11 root0Node1Domains3 root0Node1Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node1Step4Chunk0_0_checked, root0Node1Step4Chunk0_1_checked, root0Node1Step4Chunk0_2_checked, root0Node1Step4Chunk0_3_checked, root0Node1Step4Chunk0_4_checked, root0Node1Step4Chunk0_5_checked, root0Node1Step4Chunk1_0_checked, root0Node1Step4Chunk1_1_checked, root0Node1Step4Chunk1_2_checked, root0Node1Step4Chunk1_3_checked, root0Node1Step4Chunk1_4_checked, root0Node1Step4Chunk1_5_checked, root0Node1Step4Chunk2_0_checked, root0Node1Step4Chunk2_1_checked, root0Node1Step4Chunk2_2_checked, root0Node1Step4Chunk2_3_checked, root0Node1Step4Chunk2_4_checked, root0Node1Step4Chunk2_5_checked, root0Node1Step4Chunk3_0_checked, root0Node1Step4Chunk3_1_checked, root0Node1Step4Chunk3_2_checked, root0Node1Step4Chunk3_3_checked, root0Node1Step4Chunk3_4_checked, root0Node1Step4Chunk3_5_checked, root0Node1Step4Chunk4_0_checked, root0Node1Step4Chunk4_1_checked, root0Node1Step4Chunk4_2_checked, root0Node1Step4Chunk4_3_checked, root0Node1Step4Chunk4_4_checked, root0Node1Step4Chunk4_5_checked, root0Node1Step4Chunk5_0_checked, root0Node1Step4Chunk5_1_checked, root0Node1Step4Chunk5_2_checked, root0Node1Step4Chunk5_3_checked, root0Node1Step4Chunk5_4_checked, root0Node1Step4Chunk5_5_checked, root0Node1Step4Chunk6_0_checked, root0Node1Step4Chunk6_1_checked, root0Node1Step4Chunk6_2_checked, root0Node1Step4Chunk6_3_checked, root0Node1Step4Chunk6_4_checked, root0Node1Step4Chunk6_5_checked, root0Node1Step4Chunk7_0_checked, root0Node1Step4Chunk7_1_checked, root0Node1Step4Chunk7_2_checked, root0Node1Step4Chunk7_3_checked, root0Node1Step4Chunk7_4_checked, root0Node1Step4Chunk7_5_checked, root0Node1Step4Chunk8_0_checked, root0Node1Step4Chunk8_1_checked, root0Node1Step4Chunk8_2_checked, root0Node1Step4Chunk8_3_checked, root0Node1Step4Chunk8_4_checked, root0Node1Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node2Domains0 : Domains 61 State := restrict root0Node1Domains4 11 (1,1)
def root0Node2Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(2,1)]
  | 23 => some [(0,2)]
  | 24 => some [(1,1)]
  | 25 => some [(4,1)]
  | 26 => some [(4,4),(5,4),(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(3,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(5,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node2Domains0_fast_eq : root0Node2Domains0 = expandDomains root0Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node2Domains0 v = expandDomains root0Node2Domains0Fast v from by decide) v
def root0Node2Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(8,5)]
  | 11 => [(1,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(7,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(1,0)]
  | 22 => [(2,1)]
  | 23 => [(0,2)]
  | 24 => [(1,1)]
  | 25 => [(4,1)]
  | 26 => [(5,4),(8,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(3,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(5,2)]
  | 35 => [(7,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(5,4),(8,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1),(8,1)]
  | 59 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root0Node2Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(2,1)]
  | 23 => some [(0,2)]
  | 24 => some [(1,1)]
  | 25 => some [(4,1)]
  | 26 => some [(5,4),(8,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(3,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(5,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node2Domains1_fast_eq : root0Node2Domains1 = expandDomains root0Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node2Domains1 v = expandDomains root0Node2Domains1Fast v from by decide) v
theorem root0Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root0Node2Domains0 root0Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node2Domains0 root0Node2Domains1
    root0Node2Domains0Fast root0Node2Domains1Fast
    root0Node2Domains0_fast_eq root0Node2Domains1_fast_eq (by decide)
theorem root0Node2Step1_checked :
    checkReplacement table5 root0Node2Domains0 root0Node2Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node2Step1Chunk0_0_checked, root0Node2Step1Chunk0_1_checked, root0Node2Step1Chunk0_2_checked, root0Node2Step1Chunk0_3_checked, root0Node2Step1Chunk0_4_checked, root0Node2Step1Chunk0_5_checked, root0Node2Step1Chunk1_0_checked, root0Node2Step1Chunk1_1_checked, root0Node2Step1Chunk1_2_checked, root0Node2Step1Chunk1_3_checked, root0Node2Step1Chunk1_4_checked, root0Node2Step1Chunk1_5_checked, root0Node2Step1Chunk2_0_checked, root0Node2Step1Chunk2_1_checked, root0Node2Step1Chunk2_2_checked, root0Node2Step1Chunk2_3_checked, root0Node2Step1Chunk2_4_checked, root0Node2Step1Chunk2_5_checked, root0Node2Step1Chunk3_0_checked, root0Node2Step1Chunk3_1_checked, root0Node2Step1Chunk3_2_checked, root0Node2Step1Chunk3_3_checked, root0Node2Step1Chunk3_4_checked, root0Node2Step1Chunk3_5_checked, root0Node2Step1Chunk4_0_checked, root0Node2Step1Chunk4_1_checked, root0Node2Step1Chunk4_2_checked, root0Node2Step1Chunk4_3_checked, root0Node2Step1Chunk4_4_checked, root0Node2Step1Chunk4_5_checked, root0Node2Step1Chunk5_0_checked, root0Node2Step1Chunk5_1_checked, root0Node2Step1Chunk5_2_checked, root0Node2Step1Chunk5_3_checked, root0Node2Step1Chunk5_4_checked, root0Node2Step1Chunk5_5_checked, root0Node2Step1Chunk6_0_checked, root0Node2Step1Chunk6_1_checked, root0Node2Step1Chunk6_2_checked, root0Node2Step1Chunk6_3_checked, root0Node2Step1Chunk6_4_checked, root0Node2Step1Chunk6_5_checked, root0Node2Step1Chunk7_0_checked, root0Node2Step1Chunk7_1_checked, root0Node2Step1Chunk7_2_checked, root0Node2Step1Chunk7_3_checked, root0Node2Step1Chunk7_4_checked, root0Node2Step1Chunk7_5_checked, root0Node2Step1Chunk8_0_checked, root0Node2Step1Chunk8_1_checked, root0Node2Step1Chunk8_2_checked, root0Node2Step1Chunk8_3_checked, root0Node2Step1Chunk8_4_checked, root0Node2Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node3Domains0 : Domains 61 State := restrict root0Node2Domains1 26 (5,4)
def root0Node3Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(2,1)]
  | 23 => some [(0,2)]
  | 24 => some [(1,1)]
  | 25 => some [(4,1)]
  | 26 => some [(5,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(3,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(5,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4),(8,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1),(8,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node3Domains0_fast_eq : root0Node3Domains0 = expandDomains root0Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node3Domains0 v = expandDomains root0Node3Domains0Fast v from by decide) v
def root0Node3Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(8,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(4,2)]
  | 9 => [(5,3)]
  | 10 => [(8,5)]
  | 11 => [(1,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(7,2)]
  | 18 => [(8,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(1,0)]
  | 22 => [(2,1)]
  | 23 => [(0,2)]
  | 24 => [(1,1)]
  | 25 => [(4,1)]
  | 26 => [(5,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(0,0)]
  | 31 => [(3,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(5,2)]
  | 35 => [(7,5)]
  | 36 => [(6,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(1,0)]
  | 50 => [(5,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(1,3),(6,3)]
  | 55 => [(7,2),(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1)]
  | 59 => [(0,2),(6,5)]
  | _ => [(0,4),(1,1)]
def root0Node3Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(8,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(4,2)]
  | 9 => some [(5,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(7,2)]
  | 18 => some [(8,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(1,0)]
  | 22 => some [(2,1)]
  | 23 => some [(0,2)]
  | 24 => some [(1,1)]
  | 25 => some [(4,1)]
  | 26 => some [(5,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(0,0)]
  | 31 => some [(3,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(5,2)]
  | 35 => some [(7,5)]
  | 36 => some [(6,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1)]
  | 59 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root0Node3Domains1_fast_eq : root0Node3Domains1 = expandDomains root0Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node3Domains1 v = expandDomains root0Node3Domains1Fast v from by decide) v
theorem root0Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root0Node3Domains0 root0Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node3Domains0 root0Node3Domains1
    root0Node3Domains0Fast root0Node3Domains1Fast
    root0Node3Domains0_fast_eq root0Node3Domains1_fast_eq (by decide)
theorem root0Node3Step1_checked :
    checkReplacement table37 root0Node3Domains0 root0Node3Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node3Step1Chunk0_0_checked, root0Node3Step1Chunk0_1_checked, root0Node3Step1Chunk0_2_checked, root0Node3Step1Chunk0_3_checked, root0Node3Step1Chunk0_4_checked, root0Node3Step1Chunk0_5_checked, root0Node3Step1Chunk1_0_checked, root0Node3Step1Chunk1_1_checked, root0Node3Step1Chunk1_2_checked, root0Node3Step1Chunk1_3_checked, root0Node3Step1Chunk1_4_checked, root0Node3Step1Chunk1_5_checked, root0Node3Step1Chunk2_0_checked, root0Node3Step1Chunk2_1_checked, root0Node3Step1Chunk2_2_checked, root0Node3Step1Chunk2_3_checked, root0Node3Step1Chunk2_4_checked, root0Node3Step1Chunk2_5_checked, root0Node3Step1Chunk3_0_checked, root0Node3Step1Chunk3_1_checked, root0Node3Step1Chunk3_2_checked, root0Node3Step1Chunk3_3_checked, root0Node3Step1Chunk3_4_checked, root0Node3Step1Chunk3_5_checked, root0Node3Step1Chunk4_0_checked, root0Node3Step1Chunk4_1_checked, root0Node3Step1Chunk4_2_checked, root0Node3Step1Chunk4_3_checked, root0Node3Step1Chunk4_4_checked, root0Node3Step1Chunk4_5_checked, root0Node3Step1Chunk5_0_checked, root0Node3Step1Chunk5_1_checked, root0Node3Step1Chunk5_2_checked, root0Node3Step1Chunk5_3_checked, root0Node3Step1Chunk5_4_checked, root0Node3Step1Chunk5_5_checked, root0Node3Step1Chunk6_0_checked, root0Node3Step1Chunk6_1_checked, root0Node3Step1Chunk6_2_checked, root0Node3Step1Chunk6_3_checked, root0Node3Step1Chunk6_4_checked, root0Node3Step1Chunk6_5_checked, root0Node3Step1Chunk7_0_checked, root0Node3Step1Chunk7_1_checked, root0Node3Step1Chunk7_2_checked, root0Node3Step1Chunk7_3_checked, root0Node3Step1Chunk7_4_checked, root0Node3Step1Chunk7_5_checked, root0Node3Step1Chunk8_0_checked, root0Node3Step1Chunk8_1_checked, root0Node3Step1Chunk8_2_checked, root0Node3Step1Chunk8_3_checked, root0Node3Step1Chunk8_4_checked, root0Node3Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
