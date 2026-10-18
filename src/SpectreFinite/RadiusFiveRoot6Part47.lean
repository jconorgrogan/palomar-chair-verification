module

public import SpectreFinite.RadiusFiveRoot6Part46
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable46
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node113Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(4,2)]
  | 13 => [(1,1)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(1,4)]
  | 21 => [(4,0)]
  | 22 => [(7,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(3,0)]
  | 28 => [(2,5)]
  | 29 => [(6,0)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(5,3),(8,3)]
  | 41 => [(8,5)]
  | 42 => [(1,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(1,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(0,4)]
  | 62 => [(5,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3)]
  | 70 => [(4,3)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(8,1)]
  | 77 => [(6,5)]
  | 78 => [(1,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(5,5),(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(0,4)]
  | 86 => [(1,4),(3,4)]
  | 87 => [(0,5),(6,3)]
  | 88 => [(4,4),(7,2)]
  | 89 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root6Node113Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(1,1)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(1,4)]
  | 21 => some [(4,0)]
  | 22 => some [(7,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(3,0)]
  | 28 => some [(2,5)]
  | 29 => some [(6,0)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,3),(8,3)]
  | 41 => some [(8,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(1,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(0,4)]
  | 62 => some [(5,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(4,3)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(1,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(1,4),(3,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node113Domains2_fast_eq : root6Node113Domains2 = expandDomains root6Node113Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node113Domains2 v = expandDomains root6Node113Domains2Fast v from by decide) v
theorem root6Node113Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq (by decide)
theorem root6Node113Step2Narrowing_checked :
    checkNarrowing table46 root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkNarrowing_flatten table46Scope [table46Rows0_0,table46Rows0_1,table46Rows0_2,table46Rows0_3,table46Rows0_4,table46Rows0_5,table46Rows1_0,table46Rows1_1,table46Rows1_2,table46Rows1_3,table46Rows1_4,table46Rows1_5,table46Rows2_0,table46Rows2_1,table46Rows2_2,table46Rows2_3,table46Rows2_4,table46Rows2_5,table46Rows3_0,table46Rows3_1,table46Rows3_2,table46Rows3_3,table46Rows3_4,table46Rows3_5,table46Rows4_0,table46Rows4_1,table46Rows4_2,table46Rows4_3,table46Rows4_4,table46Rows4_5,table46Rows5_0,table46Rows5_1,table46Rows5_2,table46Rows5_3,table46Rows5_4,table46Rows5_5,table46Rows6_0,table46Rows6_1,table46Rows6_2,table46Rows6_3,table46Rows6_4,table46Rows6_5,table46Rows7_0,table46Rows7_1,table46Rows7_2,table46Rows7_3,table46Rows7_4,table46Rows7_5,table46Rows8_0,table46Rows8_1,table46Rows8_2,table46Rows8_3,table46Rows8_4,table46Rows8_5]
    root6Node113Domains1 root6Node113Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node113Step2Chunk0_0_checked, root6Node113Step2Chunk0_1_checked, root6Node113Step2Chunk0_2_checked, root6Node113Step2Chunk0_3_checked, root6Node113Step2Chunk0_4_checked, root6Node113Step2Chunk0_5_checked, root6Node113Step2Chunk1_0_checked, root6Node113Step2Chunk1_1_checked, root6Node113Step2Chunk1_2_checked, root6Node113Step2Chunk1_3_checked, root6Node113Step2Chunk1_4_checked, root6Node113Step2Chunk1_5_checked, root6Node113Step2Chunk2_0_checked, root6Node113Step2Chunk2_1_checked, root6Node113Step2Chunk2_2_checked, root6Node113Step2Chunk2_3_checked, root6Node113Step2Chunk2_4_checked, root6Node113Step2Chunk2_5_checked, root6Node113Step2Chunk3_0_checked, root6Node113Step2Chunk3_1_checked, root6Node113Step2Chunk3_2_checked, root6Node113Step2Chunk3_3_checked, root6Node113Step2Chunk3_4_checked, root6Node113Step2Chunk3_5_checked, root6Node113Step2Chunk4_0_checked, root6Node113Step2Chunk4_1_checked, root6Node113Step2Chunk4_2_checked, root6Node113Step2Chunk4_3_checked, root6Node113Step2Chunk4_4_checked, root6Node113Step2Chunk4_5_checked, root6Node113Step2Chunk5_0_checked, root6Node113Step2Chunk5_1_checked, root6Node113Step2Chunk5_2_checked, root6Node113Step2Chunk5_3_checked, root6Node113Step2Chunk5_4_checked, root6Node113Step2Chunk5_5_checked, root6Node113Step2Chunk6_0_checked, root6Node113Step2Chunk6_1_checked, root6Node113Step2Chunk6_2_checked, root6Node113Step2Chunk6_3_checked, root6Node113Step2Chunk6_4_checked, root6Node113Step2Chunk6_5_checked, root6Node113Step2Chunk7_0_checked, root6Node113Step2Chunk7_1_checked, root6Node113Step2Chunk7_2_checked, root6Node113Step2Chunk7_3_checked, root6Node113Step2Chunk7_4_checked, root6Node113Step2Chunk7_5_checked, root6Node113Step2Chunk8_0_checked, root6Node113Step2Chunk8_1_checked, root6Node113Step2Chunk8_2_checked, root6Node113Step2Chunk8_3_checked, root6Node113Step2Chunk8_4_checked, root6Node113Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node113Step2_checked :
    checkReplacement table46 root6Node113Domains1 root6Node113Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node113Domains1 root6Node113Domains2
    root6Node113Domains1Fast root6Node113Domains2Fast
    root6Node113Domains1_fast_eq root6Node113Domains2_fast_eq
    root6Node113Step2Narrowing_checked (by decide)
def root6Node114Domains0 : Domains 91 State := restrict root6Node113Domains2 40 (5,3)
def root6Node114Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(1,1)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(1,4)]
  | 21 => some [(4,0)]
  | 22 => some [(7,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(3,0)]
  | 28 => some [(2,5)]
  | 29 => some [(6,0)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,3)]
  | 41 => some [(8,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(1,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(0,4)]
  | 62 => some [(5,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(4,3)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(1,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(1,4),(3,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node114Domains0_fast_eq : root6Node114Domains0 = expandDomains root6Node114Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node114Domains0 v = expandDomains root6Node114Domains0Fast v from by decide) v
def root6Node115Domains0 : Domains 91 State := restrict root6Node114Domains0 81 (5,5)
def root6Node115Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(1,1)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(1,4)]
  | 21 => some [(4,0)]
  | 22 => some [(7,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(3,0)]
  | 28 => some [(2,5)]
  | 29 => some [(6,0)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,3)]
  | 41 => some [(8,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(1,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(0,4)]
  | 62 => some [(5,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(4,3)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(1,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(1,4),(3,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node115Domains0_fast_eq : root6Node115Domains0 = expandDomains root6Node115Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node115Domains0 v = expandDomains root6Node115Domains0Fast v from by decide) v
def root6Node115Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(4,2)]
  | 13 => [(1,1)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(1,4)]
  | 21 => [(4,0)]
  | 22 => [(7,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(3,0)]
  | 28 => [(2,5)]
  | 29 => [(6,0)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(5,3)]
  | 41 => [(8,5)]
  | 42 => [(1,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(1,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(0,4)]
  | 62 => [(5,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3)]
  | 70 => [(4,3)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(8,1)]
  | 77 => [(6,5)]
  | 78 => [(1,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(5,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,5)]
  | 85 => [(0,4)]
  | 86 => [(1,4)]
  | 87 => [(0,5)]
  | 88 => [(4,4)]
  | 89 => [(1,4)]
  | _ => [(0,5)]
def root6Node115Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(1,1)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(1,4)]
  | 21 => some [(4,0)]
  | 22 => some [(7,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(3,0)]
  | 28 => some [(2,5)]
  | 29 => some [(6,0)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,3)]
  | 41 => some [(8,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(1,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(0,4)]
  | 62 => some [(5,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(4,3)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(1,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5)]
  | 85 => some [(0,4)]
  | 86 => some [(1,4)]
  | 87 => some [(0,5)]
  | 88 => some [(4,4)]
  | 89 => some [(1,4)]
  | _ => some [(0,5)]
theorem root6Node115Domains1_fast_eq : root6Node115Domains1 = expandDomains root6Node115Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node115Domains1 v = expandDomains root6Node115Domains1Fast v from by decide) v
theorem root6Node115Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq (by decide)
theorem root6Node115Step1Narrowing_checked :
    checkNarrowing table56 root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root6Node115Domains0 root6Node115Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node115Step1Chunk0_0_checked, root6Node115Step1Chunk0_1_checked, root6Node115Step1Chunk0_2_checked, root6Node115Step1Chunk0_3_checked, root6Node115Step1Chunk0_4_checked, root6Node115Step1Chunk0_5_checked, root6Node115Step1Chunk1_0_checked, root6Node115Step1Chunk1_1_checked, root6Node115Step1Chunk1_2_checked, root6Node115Step1Chunk1_3_checked, root6Node115Step1Chunk1_4_checked, root6Node115Step1Chunk1_5_checked, root6Node115Step1Chunk2_0_checked, root6Node115Step1Chunk2_1_checked, root6Node115Step1Chunk2_2_checked, root6Node115Step1Chunk2_3_checked, root6Node115Step1Chunk2_4_checked, root6Node115Step1Chunk2_5_checked, root6Node115Step1Chunk3_0_checked, root6Node115Step1Chunk3_1_checked, root6Node115Step1Chunk3_2_checked, root6Node115Step1Chunk3_3_checked, root6Node115Step1Chunk3_4_checked, root6Node115Step1Chunk3_5_checked, root6Node115Step1Chunk4_0_checked, root6Node115Step1Chunk4_1_checked, root6Node115Step1Chunk4_2_checked, root6Node115Step1Chunk4_3_checked, root6Node115Step1Chunk4_4_checked, root6Node115Step1Chunk4_5_checked, root6Node115Step1Chunk5_0_checked, root6Node115Step1Chunk5_1_checked, root6Node115Step1Chunk5_2_checked, root6Node115Step1Chunk5_3_checked, root6Node115Step1Chunk5_4_checked, root6Node115Step1Chunk5_5_checked, root6Node115Step1Chunk6_0_checked, root6Node115Step1Chunk6_1_checked, root6Node115Step1Chunk6_2_checked, root6Node115Step1Chunk6_3_checked, root6Node115Step1Chunk6_4_checked, root6Node115Step1Chunk6_5_checked, root6Node115Step1Chunk7_0_checked, root6Node115Step1Chunk7_1_checked, root6Node115Step1Chunk7_2_checked, root6Node115Step1Chunk7_3_checked, root6Node115Step1Chunk7_4_checked, root6Node115Step1Chunk7_5_checked, root6Node115Step1Chunk8_0_checked, root6Node115Step1Chunk8_1_checked, root6Node115Step1Chunk8_2_checked, root6Node115Step1Chunk8_3_checked, root6Node115Step1Chunk8_4_checked, root6Node115Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node115Step1_checked :
    checkReplacement table56 root6Node115Domains0 root6Node115Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node115Domains0 root6Node115Domains1
    root6Node115Domains0Fast root6Node115Domains1Fast
    root6Node115Domains0_fast_eq root6Node115Domains1_fast_eq
    root6Node115Step1Narrowing_checked (by decide)
theorem root6Node115Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node115Domains1 (.output 56) = true := by decide
def root6Node116Domains0 : Domains 91 State := restrict root6Node114Domains0 81 (8,5)
def root6Node116Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(1,1)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(1,4)]
  | 21 => some [(4,0)]
  | 22 => some [(7,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(3,0)]
  | 28 => some [(2,5)]
  | 29 => some [(6,0)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,3)]
  | 41 => some [(8,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(1,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(0,4)]
  | 62 => some [(5,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(4,3)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(1,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(1,4),(3,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root6Node116Domains0_fast_eq : root6Node116Domains0 = expandDomains root6Node116Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node116Domains0 v = expandDomains root6Node116Domains0Fast v from by decide) v
def root6Node116Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(7,0)]
  | 4 => [(4,3)]
  | 5 => [(7,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(6,3)]
  | 9 => [(7,2)]
  | 10 => [(7,4)]
  | 11 => [(1,3)]
  | 12 => [(4,2)]
  | 13 => [(1,1)]
  | 14 => [(4,1)]
  | 15 => [(0,2)]
  | 16 => [(1,1)]
  | 17 => [(8,1)]
  | 18 => [(6,5)]
  | 19 => [(0,4)]
  | 20 => [(1,4)]
  | 21 => [(4,0)]
  | 22 => [(7,3)]
  | 23 => [(5,2)]
  | 24 => [(8,0)]
  | 25 => [(8,3)]
  | 26 => [(5,5)]
  | 27 => [(3,0)]
  | 28 => [(2,5)]
  | 29 => [(6,0)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(5,3)]
  | 41 => [(8,5)]
  | 42 => [(1,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(1,5)]
  | 48 => [(6,1)]
  | 49 => [(5,1)]
  | 50 => [(0,1)]
  | 51 => [(1,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(7,0)]
  | 59 => [(8,3)]
  | 60 => [(8,5)]
  | 61 => [(0,4)]
  | 62 => [(5,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(7,4)]
  | 69 => [(1,3)]
  | 70 => [(4,3)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(8,1)]
  | 77 => [(6,5)]
  | 78 => [(1,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(8,5)]
  | 85 => [(0,4)]
  | 86 => [(3,4)]
  | 87 => [(6,3)]
  | 88 => [(7,2)]
  | 89 => [(7,4)]
  | _ => [(6,3)]
def root6Node116Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(7,0)]
  | 4 => some [(4,3)]
  | 5 => some [(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(6,3)]
  | 9 => some [(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(1,3)]
  | 12 => some [(4,2)]
  | 13 => some [(1,1)]
  | 14 => some [(4,1)]
  | 15 => some [(0,2)]
  | 16 => some [(1,1)]
  | 17 => some [(8,1)]
  | 18 => some [(6,5)]
  | 19 => some [(0,4)]
  | 20 => some [(1,4)]
  | 21 => some [(4,0)]
  | 22 => some [(7,3)]
  | 23 => some [(5,2)]
  | 24 => some [(8,0)]
  | 25 => some [(8,3)]
  | 26 => some [(5,5)]
  | 27 => some [(3,0)]
  | 28 => some [(2,5)]
  | 29 => some [(6,0)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(5,3)]
  | 41 => some [(8,5)]
  | 42 => some [(1,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5)]
  | 48 => some [(6,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,1)]
  | 51 => some [(1,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(7,0)]
  | 59 => some [(8,3)]
  | 60 => some [(8,5)]
  | 61 => some [(0,4)]
  | 62 => some [(5,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(7,4)]
  | 69 => some [(1,3)]
  | 70 => some [(4,3)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(8,1)]
  | 77 => some [(6,5)]
  | 78 => some [(1,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(8,5)]
  | 85 => some [(0,4)]
  | 86 => some [(3,4)]
  | 87 => some [(6,3)]
  | 88 => some [(7,2)]
  | 89 => some [(7,4)]
  | _ => some [(6,3)]
theorem root6Node116Domains1_fast_eq : root6Node116Domains1 = expandDomains root6Node116Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node116Domains1 v = expandDomains root6Node116Domains1Fast v from by decide) v
theorem root6Node116Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq (by decide)
theorem root6Node116Step1Narrowing_checked :
    checkNarrowing table56 root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root6Node116Domains0 root6Node116Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node116Step1Chunk0_0_checked, root6Node116Step1Chunk0_1_checked, root6Node116Step1Chunk0_2_checked, root6Node116Step1Chunk0_3_checked, root6Node116Step1Chunk0_4_checked, root6Node116Step1Chunk0_5_checked, root6Node116Step1Chunk1_0_checked, root6Node116Step1Chunk1_1_checked, root6Node116Step1Chunk1_2_checked, root6Node116Step1Chunk1_3_checked, root6Node116Step1Chunk1_4_checked, root6Node116Step1Chunk1_5_checked, root6Node116Step1Chunk2_0_checked, root6Node116Step1Chunk2_1_checked, root6Node116Step1Chunk2_2_checked, root6Node116Step1Chunk2_3_checked, root6Node116Step1Chunk2_4_checked, root6Node116Step1Chunk2_5_checked, root6Node116Step1Chunk3_0_checked, root6Node116Step1Chunk3_1_checked, root6Node116Step1Chunk3_2_checked, root6Node116Step1Chunk3_3_checked, root6Node116Step1Chunk3_4_checked, root6Node116Step1Chunk3_5_checked, root6Node116Step1Chunk4_0_checked, root6Node116Step1Chunk4_1_checked, root6Node116Step1Chunk4_2_checked, root6Node116Step1Chunk4_3_checked, root6Node116Step1Chunk4_4_checked, root6Node116Step1Chunk4_5_checked, root6Node116Step1Chunk5_0_checked, root6Node116Step1Chunk5_1_checked, root6Node116Step1Chunk5_2_checked, root6Node116Step1Chunk5_3_checked, root6Node116Step1Chunk5_4_checked, root6Node116Step1Chunk5_5_checked, root6Node116Step1Chunk6_0_checked, root6Node116Step1Chunk6_1_checked, root6Node116Step1Chunk6_2_checked, root6Node116Step1Chunk6_3_checked, root6Node116Step1Chunk6_4_checked, root6Node116Step1Chunk6_5_checked, root6Node116Step1Chunk7_0_checked, root6Node116Step1Chunk7_1_checked, root6Node116Step1Chunk7_2_checked, root6Node116Step1Chunk7_3_checked, root6Node116Step1Chunk7_4_checked, root6Node116Step1Chunk7_5_checked, root6Node116Step1Chunk8_0_checked, root6Node116Step1Chunk8_1_checked, root6Node116Step1Chunk8_2_checked, root6Node116Step1Chunk8_3_checked, root6Node116Step1Chunk8_4_checked, root6Node116Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node116Step1_checked :
    checkReplacement table56 root6Node116Domains0 root6Node116Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node116Domains0 root6Node116Domains1
    root6Node116Domains0Fast root6Node116Domains1Fast
    root6Node116Domains0_fast_eq root6Node116Domains1_fast_eq
    root6Node116Step1Narrowing_checked (by decide)
theorem root6Node116Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node116Domains1 (.output 57) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
