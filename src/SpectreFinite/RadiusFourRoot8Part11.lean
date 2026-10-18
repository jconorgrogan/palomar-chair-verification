module

public import SpectreFinite.RadiusFourRoot8Part10
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable38
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node32Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(6,3)]
  | 27 => [(2,2)]
  | 28 => [(3,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5)]
  | 33 => [(7,0)]
  | 34 => [(4,3)]
  | 35 => [(1,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(1,4)]
  | 43 => [(4,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(7,2)]
  | 51 => [(4,0)]
  | 52 => [(7,3)]
  | 53 => [(8,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3)]
  | 56 => [(5,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(6,4)]
def root8Node32Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(6,3)]
  | 27 => some [(2,2)]
  | 28 => some [(3,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(1,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(1,4)]
  | 43 => some [(4,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(5,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(6,4)]
theorem root8Node32Domains2_fast_eq : root8Node32Domains2 = expandDomains root8Node32Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node32Domains2 v = expandDomains root8Node32Domains2Fast v from by decide) v
theorem root8Node32Step2Chunk0_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_0⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk0_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_1⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk0_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_2⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk0_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_3⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk0_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_4⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk0_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_5⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk1_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_0⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk1_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_1⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk1_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_2⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk1_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_3⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk1_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_4⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk1_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_5⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk2_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_0⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk2_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_1⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk2_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_2⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk2_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_3⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk2_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_4⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk2_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_5⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk3_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_0⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk3_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_1⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk3_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_2⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk3_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_3⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk3_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_4⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk3_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_5⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk4_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_0⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk4_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_1⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk4_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_2⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk4_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_3⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk4_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_4⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk4_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_5⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk5_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_0⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk5_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_1⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk5_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_2⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk5_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_3⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk5_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_4⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk5_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_5⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk6_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_0⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk6_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_1⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk6_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_2⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk6_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_3⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk6_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_4⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk6_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_5⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk7_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_0⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk7_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_1⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk7_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_2⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk7_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_3⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk7_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_4⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk7_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_5⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk8_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_0⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk8_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_1⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk8_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_2⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk8_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_3⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk8_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_4⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2Chunk8_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_5⟩
      root8Node32Domains1 root8Node32Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node32Domains1 root8Node32Domains2
    root8Node32Domains1Fast root8Node32Domains2Fast
    root8Node32Domains1_fast_eq root8Node32Domains2_fast_eq (by decide)
theorem root8Node32Step2_checked :
    checkReplacement table38 root8Node32Domains1 root8Node32Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node32Step2Chunk0_0_checked, root8Node32Step2Chunk0_1_checked, root8Node32Step2Chunk0_2_checked, root8Node32Step2Chunk0_3_checked, root8Node32Step2Chunk0_4_checked, root8Node32Step2Chunk0_5_checked, root8Node32Step2Chunk1_0_checked, root8Node32Step2Chunk1_1_checked, root8Node32Step2Chunk1_2_checked, root8Node32Step2Chunk1_3_checked, root8Node32Step2Chunk1_4_checked, root8Node32Step2Chunk1_5_checked, root8Node32Step2Chunk2_0_checked, root8Node32Step2Chunk2_1_checked, root8Node32Step2Chunk2_2_checked, root8Node32Step2Chunk2_3_checked, root8Node32Step2Chunk2_4_checked, root8Node32Step2Chunk2_5_checked, root8Node32Step2Chunk3_0_checked, root8Node32Step2Chunk3_1_checked, root8Node32Step2Chunk3_2_checked, root8Node32Step2Chunk3_3_checked, root8Node32Step2Chunk3_4_checked, root8Node32Step2Chunk3_5_checked, root8Node32Step2Chunk4_0_checked, root8Node32Step2Chunk4_1_checked, root8Node32Step2Chunk4_2_checked, root8Node32Step2Chunk4_3_checked, root8Node32Step2Chunk4_4_checked, root8Node32Step2Chunk4_5_checked, root8Node32Step2Chunk5_0_checked, root8Node32Step2Chunk5_1_checked, root8Node32Step2Chunk5_2_checked, root8Node32Step2Chunk5_3_checked, root8Node32Step2Chunk5_4_checked, root8Node32Step2Chunk5_5_checked, root8Node32Step2Chunk6_0_checked, root8Node32Step2Chunk6_1_checked, root8Node32Step2Chunk6_2_checked, root8Node32Step2Chunk6_3_checked, root8Node32Step2Chunk6_4_checked, root8Node32Step2Chunk6_5_checked, root8Node32Step2Chunk7_0_checked, root8Node32Step2Chunk7_1_checked, root8Node32Step2Chunk7_2_checked, root8Node32Step2Chunk7_3_checked, root8Node32Step2Chunk7_4_checked, root8Node32Step2Chunk7_5_checked, root8Node32Step2Chunk8_0_checked, root8Node32Step2Chunk8_1_checked, root8Node32Step2Chunk8_2_checked, root8Node32Step2Chunk8_3_checked, root8Node32Step2Chunk8_4_checked, root8Node32Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node32Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node32Domains2 (.output 15) = true := by decide
def root8Node33Domains0 : Domains 61 State := restrict root8Node29Domains1 3 (6,5)
def root8Node33Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4),(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3),(8,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3),(6,3)]
  | 18 => some [(3,5),(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(8,1)]
  | 24 => some [(0,2),(6,5)]
  | 25 => some [(0,4),(1,1)]
  | 26 => some [(0,5),(6,3)]
  | 27 => some [(2,2),(2,4)]
  | 28 => some [(1,3),(3,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(3,0),(5,0),(7,0)]
  | 34 => some [(2,3),(2,5),(4,3),(4,5)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0),(7,4)]
  | 52 => some [(1,3),(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,5),(7,3),(8,5)]
  | 56 => some [(5,1),(8,1)]
  | 57 => some [(0,1),(6,5)]
  | 58 => some [(0,4),(6,2)]
  | 59 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | _ => some [(0,0),(0,5),(6,3),(6,4)]
theorem root8Node33Domains0_fast_eq : root8Node33Domains0 = expandDomains root8Node33Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node33Domains0 v = expandDomains root8Node33Domains0Fast v from by decide) v
def root8Node33Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3),(6,3)]
  | 18 => [(3,5),(7,5)]
  | 19 => [(0,3)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1),(8,1)]
  | 24 => [(0,2),(6,5)]
  | 25 => [(0,4),(1,1)]
  | 26 => [(0,5),(6,3)]
  | 27 => [(2,2),(2,4)]
  | 28 => [(1,3),(3,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5)]
  | 33 => [(3,0),(5,0),(7,0)]
  | 34 => [(2,3),(2,5),(4,5)]
  | 35 => [(1,1),(7,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(8,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(4,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(7,1),(8,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2)]
  | 51 => [(4,0),(7,4)]
  | 52 => [(1,3),(7,3)]
  | 53 => [(4,2),(8,2)]
  | 54 => [(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(5,5),(7,3),(8,5)]
  | 56 => [(5,1),(8,1)]
  | 57 => [(0,1),(6,5)]
  | 58 => [(0,4),(6,2)]
  | 59 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | _ => [(0,0),(0,5),(6,3),(6,4)]
def root8Node33Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3),(6,3)]
  | 18 => some [(3,5),(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(8,1)]
  | 24 => some [(0,2),(6,5)]
  | 25 => some [(0,4),(1,1)]
  | 26 => some [(0,5),(6,3)]
  | 27 => some [(2,2),(2,4)]
  | 28 => some [(1,3),(3,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(3,0),(5,0),(7,0)]
  | 34 => some [(2,3),(2,5),(4,5)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0),(7,4)]
  | 52 => some [(1,3),(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,5),(7,3),(8,5)]
  | 56 => some [(5,1),(8,1)]
  | 57 => some [(0,1),(6,5)]
  | 58 => some [(0,4),(6,2)]
  | 59 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | _ => some [(0,0),(0,5),(6,3),(6,4)]
theorem root8Node33Domains1_fast_eq : root8Node33Domains1 = expandDomains root8Node33Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node33Domains1 v = expandDomains root8Node33Domains1Fast v from by decide) v
theorem root8Node33Step1Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root8Node33Domains0 root8Node33Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node33Domains0 root8Node33Domains1
    root8Node33Domains0Fast root8Node33Domains1Fast
    root8Node33Domains0_fast_eq root8Node33Domains1_fast_eq (by decide)
theorem root8Node33Step1_checked :
    checkReplacement table16 root8Node33Domains0 root8Node33Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node33Step1Chunk0_0_checked, root8Node33Step1Chunk0_1_checked, root8Node33Step1Chunk0_2_checked, root8Node33Step1Chunk0_3_checked, root8Node33Step1Chunk0_4_checked, root8Node33Step1Chunk0_5_checked, root8Node33Step1Chunk1_0_checked, root8Node33Step1Chunk1_1_checked, root8Node33Step1Chunk1_2_checked, root8Node33Step1Chunk1_3_checked, root8Node33Step1Chunk1_4_checked, root8Node33Step1Chunk1_5_checked, root8Node33Step1Chunk2_0_checked, root8Node33Step1Chunk2_1_checked, root8Node33Step1Chunk2_2_checked, root8Node33Step1Chunk2_3_checked, root8Node33Step1Chunk2_4_checked, root8Node33Step1Chunk2_5_checked, root8Node33Step1Chunk3_0_checked, root8Node33Step1Chunk3_1_checked, root8Node33Step1Chunk3_2_checked, root8Node33Step1Chunk3_3_checked, root8Node33Step1Chunk3_4_checked, root8Node33Step1Chunk3_5_checked, root8Node33Step1Chunk4_0_checked, root8Node33Step1Chunk4_1_checked, root8Node33Step1Chunk4_2_checked, root8Node33Step1Chunk4_3_checked, root8Node33Step1Chunk4_4_checked, root8Node33Step1Chunk4_5_checked, root8Node33Step1Chunk5_0_checked, root8Node33Step1Chunk5_1_checked, root8Node33Step1Chunk5_2_checked, root8Node33Step1Chunk5_3_checked, root8Node33Step1Chunk5_4_checked, root8Node33Step1Chunk5_5_checked, root8Node33Step1Chunk6_0_checked, root8Node33Step1Chunk6_1_checked, root8Node33Step1Chunk6_2_checked, root8Node33Step1Chunk6_3_checked, root8Node33Step1Chunk6_4_checked, root8Node33Step1Chunk6_5_checked, root8Node33Step1Chunk7_0_checked, root8Node33Step1Chunk7_1_checked, root8Node33Step1Chunk7_2_checked, root8Node33Step1Chunk7_3_checked, root8Node33Step1Chunk7_4_checked, root8Node33Step1Chunk7_5_checked, root8Node33Step1Chunk8_0_checked, root8Node33Step1Chunk8_1_checked, root8Node33Step1Chunk8_2_checked, root8Node33Step1Chunk8_3_checked, root8Node33Step1Chunk8_4_checked, root8Node33Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node34Domains0 : Domains 61 State := restrict root8Node33Domains1 17 (1,3)
def root8Node34Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(3,5),(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(8,1)]
  | 24 => some [(0,2),(6,5)]
  | 25 => some [(0,4),(1,1)]
  | 26 => some [(0,5),(6,3)]
  | 27 => some [(2,2),(2,4)]
  | 28 => some [(1,3),(3,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(3,0),(5,0),(7,0)]
  | 34 => some [(2,3),(2,5),(4,5)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0),(7,4)]
  | 52 => some [(1,3),(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,5),(7,3),(8,5)]
  | 56 => some [(5,1),(8,1)]
  | 57 => some [(0,1),(6,5)]
  | 58 => some [(0,4),(6,2)]
  | 59 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | _ => some [(0,0),(0,5),(6,3),(6,4)]
theorem root8Node34Domains0_fast_eq : root8Node34Domains0 = expandDomains root8Node34Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node34Domains0 v = expandDomains root8Node34Domains0Fast v from by decide) v
def root8Node34Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(3,5),(7,5)]
  | 19 => [(0,3)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(0,5),(6,3)]
  | 27 => [(2,2),(2,4)]
  | 28 => [(1,3),(3,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5)]
  | 33 => [(3,0),(7,0)]
  | 34 => [(2,3),(2,5)]
  | 35 => [(1,1),(7,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(4,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2)]
  | 51 => [(4,0),(7,4)]
  | 52 => [(1,3),(7,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0),(8,0)]
  | 55 => [(4,5),(7,3)]
  | 56 => [(5,1),(8,1)]
  | 57 => [(0,1),(6,5)]
  | 58 => [(0,4),(6,2)]
  | 59 => [(5,4),(8,4)]
  | _ => [(0,0),(6,4)]
def root8Node34Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(3,5),(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(0,5),(6,3)]
  | 27 => some [(2,2),(2,4)]
  | 28 => some [(1,3),(3,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(3,0),(7,0)]
  | 34 => some [(2,3),(2,5)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0),(7,4)]
  | 52 => some [(1,3),(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(5,1),(8,1)]
  | 57 => some [(0,1),(6,5)]
  | 58 => some [(0,4),(6,2)]
  | 59 => some [(5,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root8Node34Domains1_fast_eq : root8Node34Domains1 = expandDomains root8Node34Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node34Domains1 v = expandDomains root8Node34Domains1Fast v from by decide) v
theorem root8Node34Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root8Node34Domains0 root8Node34Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node34Domains0 root8Node34Domains1
    root8Node34Domains0Fast root8Node34Domains1Fast
    root8Node34Domains0_fast_eq root8Node34Domains1_fast_eq (by decide)
theorem root8Node34Step1_checked :
    checkReplacement table40 root8Node34Domains0 root8Node34Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node34Step1Chunk0_0_checked, root8Node34Step1Chunk0_1_checked, root8Node34Step1Chunk0_2_checked, root8Node34Step1Chunk0_3_checked, root8Node34Step1Chunk0_4_checked, root8Node34Step1Chunk0_5_checked, root8Node34Step1Chunk1_0_checked, root8Node34Step1Chunk1_1_checked, root8Node34Step1Chunk1_2_checked, root8Node34Step1Chunk1_3_checked, root8Node34Step1Chunk1_4_checked, root8Node34Step1Chunk1_5_checked, root8Node34Step1Chunk2_0_checked, root8Node34Step1Chunk2_1_checked, root8Node34Step1Chunk2_2_checked, root8Node34Step1Chunk2_3_checked, root8Node34Step1Chunk2_4_checked, root8Node34Step1Chunk2_5_checked, root8Node34Step1Chunk3_0_checked, root8Node34Step1Chunk3_1_checked, root8Node34Step1Chunk3_2_checked, root8Node34Step1Chunk3_3_checked, root8Node34Step1Chunk3_4_checked, root8Node34Step1Chunk3_5_checked, root8Node34Step1Chunk4_0_checked, root8Node34Step1Chunk4_1_checked, root8Node34Step1Chunk4_2_checked, root8Node34Step1Chunk4_3_checked, root8Node34Step1Chunk4_4_checked, root8Node34Step1Chunk4_5_checked, root8Node34Step1Chunk5_0_checked, root8Node34Step1Chunk5_1_checked, root8Node34Step1Chunk5_2_checked, root8Node34Step1Chunk5_3_checked, root8Node34Step1Chunk5_4_checked, root8Node34Step1Chunk5_5_checked, root8Node34Step1Chunk6_0_checked, root8Node34Step1Chunk6_1_checked, root8Node34Step1Chunk6_2_checked, root8Node34Step1Chunk6_3_checked, root8Node34Step1Chunk6_4_checked, root8Node34Step1Chunk6_5_checked, root8Node34Step1Chunk7_0_checked, root8Node34Step1Chunk7_1_checked, root8Node34Step1Chunk7_2_checked, root8Node34Step1Chunk7_3_checked, root8Node34Step1Chunk7_4_checked, root8Node34Step1Chunk7_5_checked, root8Node34Step1Chunk8_0_checked, root8Node34Step1Chunk8_1_checked, root8Node34Step1Chunk8_2_checked, root8Node34Step1Chunk8_3_checked, root8Node34Step1Chunk8_4_checked, root8Node34Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node35Domains0 : Domains 61 State := restrict root8Node34Domains1 18 (3,5)
def root8Node35Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(3,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(0,5),(6,3)]
  | 27 => some [(2,2),(2,4)]
  | 28 => some [(1,3),(3,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(3,0),(7,0)]
  | 34 => some [(2,3),(2,5)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(4,0),(7,4)]
  | 52 => some [(1,3),(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(5,1),(8,1)]
  | 57 => some [(0,1),(6,5)]
  | 58 => some [(0,4),(6,2)]
  | 59 => some [(5,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root8Node35Domains0_fast_eq : root8Node35Domains0 = expandDomains root8Node35Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node35Domains0 v = expandDomains root8Node35Domains0Fast v from by decide) v
def root8Node35Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(3,5)]
  | 19 => [(0,3)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(0,5)]
  | 27 => [(2,4)]
  | 28 => [(1,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5)]
  | 33 => [(3,0),(7,0)]
  | 34 => [(2,3),(2,5)]
  | 35 => [(7,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(4,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0),(8,0)]
  | 55 => [(4,5),(7,3)]
  | 56 => [(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(5,4),(8,4)]
  | _ => [(0,0),(6,4)]
def root8Node35Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(3,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(0,5)]
  | 27 => some [(2,4)]
  | 28 => some [(1,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(3,0),(7,0)]
  | 34 => some [(2,3),(2,5)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(5,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root8Node35Domains1_fast_eq : root8Node35Domains1 = expandDomains root8Node35Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node35Domains1 v = expandDomains root8Node35Domains1Fast v from by decide) v
theorem root8Node35Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root8Node35Domains0 root8Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains0 root8Node35Domains1
    root8Node35Domains0Fast root8Node35Domains1Fast
    root8Node35Domains0_fast_eq root8Node35Domains1_fast_eq (by decide)
theorem root8Node35Step1_checked :
    checkReplacement table37 root8Node35Domains0 root8Node35Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node35Step1Chunk0_0_checked, root8Node35Step1Chunk0_1_checked, root8Node35Step1Chunk0_2_checked, root8Node35Step1Chunk0_3_checked, root8Node35Step1Chunk0_4_checked, root8Node35Step1Chunk0_5_checked, root8Node35Step1Chunk1_0_checked, root8Node35Step1Chunk1_1_checked, root8Node35Step1Chunk1_2_checked, root8Node35Step1Chunk1_3_checked, root8Node35Step1Chunk1_4_checked, root8Node35Step1Chunk1_5_checked, root8Node35Step1Chunk2_0_checked, root8Node35Step1Chunk2_1_checked, root8Node35Step1Chunk2_2_checked, root8Node35Step1Chunk2_3_checked, root8Node35Step1Chunk2_4_checked, root8Node35Step1Chunk2_5_checked, root8Node35Step1Chunk3_0_checked, root8Node35Step1Chunk3_1_checked, root8Node35Step1Chunk3_2_checked, root8Node35Step1Chunk3_3_checked, root8Node35Step1Chunk3_4_checked, root8Node35Step1Chunk3_5_checked, root8Node35Step1Chunk4_0_checked, root8Node35Step1Chunk4_1_checked, root8Node35Step1Chunk4_2_checked, root8Node35Step1Chunk4_3_checked, root8Node35Step1Chunk4_4_checked, root8Node35Step1Chunk4_5_checked, root8Node35Step1Chunk5_0_checked, root8Node35Step1Chunk5_1_checked, root8Node35Step1Chunk5_2_checked, root8Node35Step1Chunk5_3_checked, root8Node35Step1Chunk5_4_checked, root8Node35Step1Chunk5_5_checked, root8Node35Step1Chunk6_0_checked, root8Node35Step1Chunk6_1_checked, root8Node35Step1Chunk6_2_checked, root8Node35Step1Chunk6_3_checked, root8Node35Step1Chunk6_4_checked, root8Node35Step1Chunk6_5_checked, root8Node35Step1Chunk7_0_checked, root8Node35Step1Chunk7_1_checked, root8Node35Step1Chunk7_2_checked, root8Node35Step1Chunk7_3_checked, root8Node35Step1Chunk7_4_checked, root8Node35Step1Chunk7_5_checked, root8Node35Step1Chunk8_0_checked, root8Node35Step1Chunk8_1_checked, root8Node35Step1Chunk8_2_checked, root8Node35Step1Chunk8_3_checked, root8Node35Step1Chunk8_4_checked, root8Node35Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node35Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(1,3)]
  | 18 => [(3,5)]
  | 19 => [(0,3)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(8,1)]
  | 24 => [(6,5)]
  | 25 => [(0,4)]
  | 26 => [(0,5)]
  | 27 => [(2,4)]
  | 28 => [(1,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(8,3)]
  | 32 => [(5,5)]
  | 33 => [(3,0),(7,0)]
  | 34 => [(2,3),(2,5)]
  | 35 => [(7,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(4,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(4,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0),(8,0)]
  | 55 => [(4,5),(7,3)]
  | 56 => [(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(5,4)]
  | _ => [(0,0),(6,4)]
def root8Node35Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(1,3)]
  | 18 => some [(3,5)]
  | 19 => some [(0,3)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(8,1)]
  | 24 => some [(6,5)]
  | 25 => some [(0,4)]
  | 26 => some [(0,5)]
  | 27 => some [(2,4)]
  | 28 => some [(1,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(8,3)]
  | 32 => some [(5,5)]
  | 33 => some [(3,0),(7,0)]
  | 34 => some [(2,3),(2,5)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(4,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(5,4)]
  | _ => some [(0,0),(6,4)]
theorem root8Node35Domains2_fast_eq : root8Node35Domains2 = expandDomains root8Node35Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node35Domains2 v = expandDomains root8Node35Domains2Fast v from by decide) v
theorem root8Node35Step2Chunk0_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_0⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk0_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_1⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk0_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_2⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk0_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_3⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk0_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_4⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk0_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_5⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk1_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_0⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk1_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_1⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk1_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_2⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk1_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_3⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk1_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_4⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk1_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_5⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk2_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_0⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk2_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_1⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk2_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_2⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk2_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_3⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk2_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_4⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk2_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_5⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk3_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_0⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk3_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_1⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk3_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_2⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk3_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_3⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk3_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_4⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk3_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_5⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk4_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_0⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk4_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_1⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk4_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_2⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk4_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_3⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk4_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_4⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk4_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_5⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk5_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_0⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk5_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_1⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk5_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_2⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk5_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_3⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk5_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_4⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk5_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_5⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk6_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_0⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk6_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_1⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk6_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_2⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk6_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_3⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk6_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_4⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk6_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_5⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk7_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_0⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk7_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_1⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk7_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_2⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk7_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_3⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk7_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_4⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk7_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_5⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk8_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_0⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk8_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_1⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk8_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_2⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk8_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_3⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk8_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_4⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2Chunk8_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_5⟩
      root8Node35Domains1 root8Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node35Domains1 root8Node35Domains2
    root8Node35Domains1Fast root8Node35Domains2Fast
    root8Node35Domains1_fast_eq root8Node35Domains2_fast_eq (by decide)
theorem root8Node35Step2_checked :
    checkReplacement table38 root8Node35Domains1 root8Node35Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node35Step2Chunk0_0_checked, root8Node35Step2Chunk0_1_checked, root8Node35Step2Chunk0_2_checked, root8Node35Step2Chunk0_3_checked, root8Node35Step2Chunk0_4_checked, root8Node35Step2Chunk0_5_checked, root8Node35Step2Chunk1_0_checked, root8Node35Step2Chunk1_1_checked, root8Node35Step2Chunk1_2_checked, root8Node35Step2Chunk1_3_checked, root8Node35Step2Chunk1_4_checked, root8Node35Step2Chunk1_5_checked, root8Node35Step2Chunk2_0_checked, root8Node35Step2Chunk2_1_checked, root8Node35Step2Chunk2_2_checked, root8Node35Step2Chunk2_3_checked, root8Node35Step2Chunk2_4_checked, root8Node35Step2Chunk2_5_checked, root8Node35Step2Chunk3_0_checked, root8Node35Step2Chunk3_1_checked, root8Node35Step2Chunk3_2_checked, root8Node35Step2Chunk3_3_checked, root8Node35Step2Chunk3_4_checked, root8Node35Step2Chunk3_5_checked, root8Node35Step2Chunk4_0_checked, root8Node35Step2Chunk4_1_checked, root8Node35Step2Chunk4_2_checked, root8Node35Step2Chunk4_3_checked, root8Node35Step2Chunk4_4_checked, root8Node35Step2Chunk4_5_checked, root8Node35Step2Chunk5_0_checked, root8Node35Step2Chunk5_1_checked, root8Node35Step2Chunk5_2_checked, root8Node35Step2Chunk5_3_checked, root8Node35Step2Chunk5_4_checked, root8Node35Step2Chunk5_5_checked, root8Node35Step2Chunk6_0_checked, root8Node35Step2Chunk6_1_checked, root8Node35Step2Chunk6_2_checked, root8Node35Step2Chunk6_3_checked, root8Node35Step2Chunk6_4_checked, root8Node35Step2Chunk6_5_checked, root8Node35Step2Chunk7_0_checked, root8Node35Step2Chunk7_1_checked, root8Node35Step2Chunk7_2_checked, root8Node35Step2Chunk7_3_checked, root8Node35Step2Chunk7_4_checked, root8Node35Step2Chunk7_5_checked, root8Node35Step2Chunk8_0_checked, root8Node35Step2Chunk8_1_checked, root8Node35Step2Chunk8_2_checked, root8Node35Step2Chunk8_3_checked, root8Node35Step2Chunk8_4_checked, root8Node35Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
