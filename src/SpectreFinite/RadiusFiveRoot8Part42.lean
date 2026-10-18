module

public import SpectreFinite.RadiusFiveRoot8Part41
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node111Domains0 : Domains 91 State := restrict root8Node109Domains2 76 (8,5)
def root8Node111Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(1,4),(3,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(3,0),(7,0)]
  | 88 => some [(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node111Domains0_fast_eq : root8Node111Domains0 = expandDomains root8Node111Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node111Domains0 v = expandDomains root8Node111Domains0Fast v from by decide) v
def root8Node111Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(3,4)]
  | 13 => [(1,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3)]
  | 20 => [(0,2)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(4,3)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(6,3)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(1,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(3,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(2,3)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node111Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(6,3)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(1,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(3,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(2,3)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node111Domains1_fast_eq : root8Node111Domains1 = expandDomains root8Node111Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node111Domains1 v = expandDomains root8Node111Domains1Fast v from by decide) v
theorem root8Node111Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq (by decide)
theorem root8Node111Step1Narrowing_checked :
    checkNarrowing table56 root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node111Domains0 root8Node111Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node111Step1Chunk0_0_checked, root8Node111Step1Chunk0_1_checked, root8Node111Step1Chunk0_2_checked, root8Node111Step1Chunk0_3_checked, root8Node111Step1Chunk0_4_checked, root8Node111Step1Chunk0_5_checked, root8Node111Step1Chunk1_0_checked, root8Node111Step1Chunk1_1_checked, root8Node111Step1Chunk1_2_checked, root8Node111Step1Chunk1_3_checked, root8Node111Step1Chunk1_4_checked, root8Node111Step1Chunk1_5_checked, root8Node111Step1Chunk2_0_checked, root8Node111Step1Chunk2_1_checked, root8Node111Step1Chunk2_2_checked, root8Node111Step1Chunk2_3_checked, root8Node111Step1Chunk2_4_checked, root8Node111Step1Chunk2_5_checked, root8Node111Step1Chunk3_0_checked, root8Node111Step1Chunk3_1_checked, root8Node111Step1Chunk3_2_checked, root8Node111Step1Chunk3_3_checked, root8Node111Step1Chunk3_4_checked, root8Node111Step1Chunk3_5_checked, root8Node111Step1Chunk4_0_checked, root8Node111Step1Chunk4_1_checked, root8Node111Step1Chunk4_2_checked, root8Node111Step1Chunk4_3_checked, root8Node111Step1Chunk4_4_checked, root8Node111Step1Chunk4_5_checked, root8Node111Step1Chunk5_0_checked, root8Node111Step1Chunk5_1_checked, root8Node111Step1Chunk5_2_checked, root8Node111Step1Chunk5_3_checked, root8Node111Step1Chunk5_4_checked, root8Node111Step1Chunk5_5_checked, root8Node111Step1Chunk6_0_checked, root8Node111Step1Chunk6_1_checked, root8Node111Step1Chunk6_2_checked, root8Node111Step1Chunk6_3_checked, root8Node111Step1Chunk6_4_checked, root8Node111Step1Chunk6_5_checked, root8Node111Step1Chunk7_0_checked, root8Node111Step1Chunk7_1_checked, root8Node111Step1Chunk7_2_checked, root8Node111Step1Chunk7_3_checked, root8Node111Step1Chunk7_4_checked, root8Node111Step1Chunk7_5_checked, root8Node111Step1Chunk8_0_checked, root8Node111Step1Chunk8_1_checked, root8Node111Step1Chunk8_2_checked, root8Node111Step1Chunk8_3_checked, root8Node111Step1Chunk8_4_checked, root8Node111Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node111Step1_checked :
    checkReplacement table56 root8Node111Domains0 root8Node111Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node111Domains0 root8Node111Domains1
    root8Node111Domains0Fast root8Node111Domains1Fast
    root8Node111Domains0_fast_eq root8Node111Domains1_fast_eq
    root8Node111Step1Narrowing_checked (by decide)
theorem root8Node111Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node111Domains1 (.output 54) = true := by decide
def root8Node112Domains0 : Domains 91 State := restrict root8Node108Domains1 59 (6,3)
def root8Node112Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(6,5)]
  | 69 => some [(0,4),(1,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2)]
  | 87 => some [(3,0),(5,0),(7,0)]
  | 88 => some [(2,3),(2,5),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node112Domains0_fast_eq : root8Node112Domains0 = expandDomains root8Node112Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node112Domains0 v = expandDomains root8Node112Domains0Fast v from by decide) v
def root8Node112Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(3,4)]
  | 13 => [(1,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3)]
  | 20 => [(0,2)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(4,3)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5),(6,3)]
  | 71 => [(4,4),(7,2)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(6,3)]
  | 74 => [(2,2),(2,4)]
  | 75 => [(1,3),(3,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(1,1),(7,1)]
  | 79 => [(4,1),(7,5)]
  | 80 => [(0,2),(6,0)]
  | 81 => [(1,1),(7,1)]
  | 82 => [(0,1),(6,5)]
  | 83 => [(0,4),(6,2)]
  | 84 => [(5,4),(8,4)]
  | 85 => [(7,3),(8,3)]
  | 86 => [(5,2),(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0),(7,0)]
  | _ => [(4,3),(7,1)]
def root8Node112Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(6,3)]
  | 74 => some [(2,2),(2,4)]
  | 75 => some [(1,3),(3,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5)]
  | 80 => some [(0,2),(6,0)]
  | 81 => some [(1,1),(7,1)]
  | 82 => some [(0,1),(6,5)]
  | 83 => some [(0,4),(6,2)]
  | 84 => some [(5,4),(8,4)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node112Domains1_fast_eq : root8Node112Domains1 = expandDomains root8Node112Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node112Domains1 v = expandDomains root8Node112Domains1Fast v from by decide) v
theorem root8Node112Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq (by decide)
theorem root8Node112Step1Narrowing_checked :
    checkNarrowing table56 root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node112Domains0 root8Node112Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node112Step1Chunk0_0_checked, root8Node112Step1Chunk0_1_checked, root8Node112Step1Chunk0_2_checked, root8Node112Step1Chunk0_3_checked, root8Node112Step1Chunk0_4_checked, root8Node112Step1Chunk0_5_checked, root8Node112Step1Chunk1_0_checked, root8Node112Step1Chunk1_1_checked, root8Node112Step1Chunk1_2_checked, root8Node112Step1Chunk1_3_checked, root8Node112Step1Chunk1_4_checked, root8Node112Step1Chunk1_5_checked, root8Node112Step1Chunk2_0_checked, root8Node112Step1Chunk2_1_checked, root8Node112Step1Chunk2_2_checked, root8Node112Step1Chunk2_3_checked, root8Node112Step1Chunk2_4_checked, root8Node112Step1Chunk2_5_checked, root8Node112Step1Chunk3_0_checked, root8Node112Step1Chunk3_1_checked, root8Node112Step1Chunk3_2_checked, root8Node112Step1Chunk3_3_checked, root8Node112Step1Chunk3_4_checked, root8Node112Step1Chunk3_5_checked, root8Node112Step1Chunk4_0_checked, root8Node112Step1Chunk4_1_checked, root8Node112Step1Chunk4_2_checked, root8Node112Step1Chunk4_3_checked, root8Node112Step1Chunk4_4_checked, root8Node112Step1Chunk4_5_checked, root8Node112Step1Chunk5_0_checked, root8Node112Step1Chunk5_1_checked, root8Node112Step1Chunk5_2_checked, root8Node112Step1Chunk5_3_checked, root8Node112Step1Chunk5_4_checked, root8Node112Step1Chunk5_5_checked, root8Node112Step1Chunk6_0_checked, root8Node112Step1Chunk6_1_checked, root8Node112Step1Chunk6_2_checked, root8Node112Step1Chunk6_3_checked, root8Node112Step1Chunk6_4_checked, root8Node112Step1Chunk6_5_checked, root8Node112Step1Chunk7_0_checked, root8Node112Step1Chunk7_1_checked, root8Node112Step1Chunk7_2_checked, root8Node112Step1Chunk7_3_checked, root8Node112Step1Chunk7_4_checked, root8Node112Step1Chunk7_5_checked, root8Node112Step1Chunk8_0_checked, root8Node112Step1Chunk8_1_checked, root8Node112Step1Chunk8_2_checked, root8Node112Step1Chunk8_3_checked, root8Node112Step1Chunk8_4_checked, root8Node112Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node112Step1_checked :
    checkReplacement table56 root8Node112Domains0 root8Node112Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node112Domains0 root8Node112Domains1
    root8Node112Domains0Fast root8Node112Domains1Fast
    root8Node112Domains0_fast_eq root8Node112Domains1_fast_eq
    root8Node112Step1Narrowing_checked (by decide)
def root8Node112Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(3,4)]
  | 13 => [(1,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3)]
  | 20 => [(0,2)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(4,3)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5),(6,3)]
  | 71 => [(4,4),(7,2)]
  | 72 => [(1,4),(7,4)]
  | 73 => [(0,5),(6,3)]
  | 74 => [(2,2),(2,4)]
  | 75 => [(1,3),(3,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(1,1),(7,1)]
  | 79 => [(4,1),(7,5)]
  | 80 => [(0,2),(6,0)]
  | 81 => [(1,1),(7,1)]
  | 82 => [(0,1),(6,5)]
  | 83 => [(0,4),(6,2)]
  | 84 => [(5,4),(8,4)]
  | 85 => [(7,3)]
  | 86 => [(5,2),(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0),(7,0)]
  | _ => [(4,3),(7,1)]
def root8Node112Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(6,3)]
  | 74 => some [(2,2),(2,4)]
  | 75 => some [(1,3),(3,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5)]
  | 80 => some [(0,2),(6,0)]
  | 81 => some [(1,1),(7,1)]
  | 82 => some [(0,1),(6,5)]
  | 83 => some [(0,4),(6,2)]
  | 84 => some [(5,4),(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node112Domains2_fast_eq : root8Node112Domains2 = expandDomains root8Node112Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node112Domains2 v = expandDomains root8Node112Domains2Fast v from by decide) v
theorem root8Node112Step2Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq (by decide)
theorem root8Node112Step2Narrowing_checked :
    checkNarrowing table51 root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root8Node112Domains1 root8Node112Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node112Step2Chunk0_0_checked, root8Node112Step2Chunk0_1_checked, root8Node112Step2Chunk0_2_checked, root8Node112Step2Chunk0_3_checked, root8Node112Step2Chunk0_4_checked, root8Node112Step2Chunk0_5_checked, root8Node112Step2Chunk1_0_checked, root8Node112Step2Chunk1_1_checked, root8Node112Step2Chunk1_2_checked, root8Node112Step2Chunk1_3_checked, root8Node112Step2Chunk1_4_checked, root8Node112Step2Chunk1_5_checked, root8Node112Step2Chunk2_0_checked, root8Node112Step2Chunk2_1_checked, root8Node112Step2Chunk2_2_checked, root8Node112Step2Chunk2_3_checked, root8Node112Step2Chunk2_4_checked, root8Node112Step2Chunk2_5_checked, root8Node112Step2Chunk3_0_checked, root8Node112Step2Chunk3_1_checked, root8Node112Step2Chunk3_2_checked, root8Node112Step2Chunk3_3_checked, root8Node112Step2Chunk3_4_checked, root8Node112Step2Chunk3_5_checked, root8Node112Step2Chunk4_0_checked, root8Node112Step2Chunk4_1_checked, root8Node112Step2Chunk4_2_checked, root8Node112Step2Chunk4_3_checked, root8Node112Step2Chunk4_4_checked, root8Node112Step2Chunk4_5_checked, root8Node112Step2Chunk5_0_checked, root8Node112Step2Chunk5_1_checked, root8Node112Step2Chunk5_2_checked, root8Node112Step2Chunk5_3_checked, root8Node112Step2Chunk5_4_checked, root8Node112Step2Chunk5_5_checked, root8Node112Step2Chunk6_0_checked, root8Node112Step2Chunk6_1_checked, root8Node112Step2Chunk6_2_checked, root8Node112Step2Chunk6_3_checked, root8Node112Step2Chunk6_4_checked, root8Node112Step2Chunk6_5_checked, root8Node112Step2Chunk7_0_checked, root8Node112Step2Chunk7_1_checked, root8Node112Step2Chunk7_2_checked, root8Node112Step2Chunk7_3_checked, root8Node112Step2Chunk7_4_checked, root8Node112Step2Chunk7_5_checked, root8Node112Step2Chunk8_0_checked, root8Node112Step2Chunk8_1_checked, root8Node112Step2Chunk8_2_checked, root8Node112Step2Chunk8_3_checked, root8Node112Step2Chunk8_4_checked, root8Node112Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node112Step2_checked :
    checkReplacement table51 root8Node112Domains1 root8Node112Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node112Domains1 root8Node112Domains2
    root8Node112Domains1Fast root8Node112Domains2Fast
    root8Node112Domains1_fast_eq root8Node112Domains2_fast_eq
    root8Node112Step2Narrowing_checked (by decide)
def root8Node113Domains0 : Domains 91 State := restrict root8Node112Domains2 62 (5,5)
def root8Node113Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5),(6,3)]
  | 71 => some [(4,4),(7,2)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(6,3)]
  | 74 => some [(2,2),(2,4)]
  | 75 => some [(1,3),(3,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(1,1),(7,1)]
  | 79 => some [(4,1),(7,5)]
  | 80 => some [(0,2),(6,0)]
  | 81 => some [(1,1),(7,1)]
  | 82 => some [(0,1),(6,5)]
  | 83 => some [(0,4),(6,2)]
  | 84 => some [(5,4),(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(5,2),(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0),(7,0)]
  | _ => some [(4,3),(7,1)]
theorem root8Node113Domains0_fast_eq : root8Node113Domains0 = expandDomains root8Node113Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node113Domains0 v = expandDomains root8Node113Domains0Fast v from by decide) v
def root8Node113Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(3,4)]
  | 13 => [(1,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3)]
  | 20 => [(0,2)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(7,0)]
  | 32 => [(4,3)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(3,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,4)]
  | 75 => [(1,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(7,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4)]
  | 84 => [(5,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(7,0)]
  | _ => [(4,3)]
def root8Node113Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(1,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(7,0)]
  | 32 => some [(4,3)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(3,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,4)]
  | 75 => some [(1,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(7,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4)]
  | 84 => some [(5,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(7,0)]
  | _ => some [(4,3)]
theorem root8Node113Domains1_fast_eq : root8Node113Domains1 = expandDomains root8Node113Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node113Domains1 v = expandDomains root8Node113Domains1Fast v from by decide) v
theorem root8Node113Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq (by decide)
theorem root8Node113Step1Narrowing_checked :
    checkNarrowing table65 root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root8Node113Domains0 root8Node113Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node113Step1Chunk0_0_checked, root8Node113Step1Chunk0_1_checked, root8Node113Step1Chunk0_2_checked, root8Node113Step1Chunk0_3_checked, root8Node113Step1Chunk0_4_checked, root8Node113Step1Chunk0_5_checked, root8Node113Step1Chunk1_0_checked, root8Node113Step1Chunk1_1_checked, root8Node113Step1Chunk1_2_checked, root8Node113Step1Chunk1_3_checked, root8Node113Step1Chunk1_4_checked, root8Node113Step1Chunk1_5_checked, root8Node113Step1Chunk2_0_checked, root8Node113Step1Chunk2_1_checked, root8Node113Step1Chunk2_2_checked, root8Node113Step1Chunk2_3_checked, root8Node113Step1Chunk2_4_checked, root8Node113Step1Chunk2_5_checked, root8Node113Step1Chunk3_0_checked, root8Node113Step1Chunk3_1_checked, root8Node113Step1Chunk3_2_checked, root8Node113Step1Chunk3_3_checked, root8Node113Step1Chunk3_4_checked, root8Node113Step1Chunk3_5_checked, root8Node113Step1Chunk4_0_checked, root8Node113Step1Chunk4_1_checked, root8Node113Step1Chunk4_2_checked, root8Node113Step1Chunk4_3_checked, root8Node113Step1Chunk4_4_checked, root8Node113Step1Chunk4_5_checked, root8Node113Step1Chunk5_0_checked, root8Node113Step1Chunk5_1_checked, root8Node113Step1Chunk5_2_checked, root8Node113Step1Chunk5_3_checked, root8Node113Step1Chunk5_4_checked, root8Node113Step1Chunk5_5_checked, root8Node113Step1Chunk6_0_checked, root8Node113Step1Chunk6_1_checked, root8Node113Step1Chunk6_2_checked, root8Node113Step1Chunk6_3_checked, root8Node113Step1Chunk6_4_checked, root8Node113Step1Chunk6_5_checked, root8Node113Step1Chunk7_0_checked, root8Node113Step1Chunk7_1_checked, root8Node113Step1Chunk7_2_checked, root8Node113Step1Chunk7_3_checked, root8Node113Step1Chunk7_4_checked, root8Node113Step1Chunk7_5_checked, root8Node113Step1Chunk8_0_checked, root8Node113Step1Chunk8_1_checked, root8Node113Step1Chunk8_2_checked, root8Node113Step1Chunk8_3_checked, root8Node113Step1Chunk8_4_checked, root8Node113Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node113Step1_checked :
    checkReplacement table65 root8Node113Domains0 root8Node113Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node113Domains0 root8Node113Domains1
    root8Node113Domains0Fast root8Node113Domains1Fast
    root8Node113Domains0_fast_eq root8Node113Domains1_fast_eq
    root8Node113Step1Narrowing_checked (by decide)
theorem root8Node113Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node113Domains1 (.output 55) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
