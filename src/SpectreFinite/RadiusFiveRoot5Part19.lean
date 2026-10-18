module

public import SpectreFinite.RadiusFiveRoot5Part18
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node43Domains0 : Domains 91 State := restrict root5Node42Domains1 40 (1,3)
def root5Node43Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(3,5)]
  | 18 => some [(0,3)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,4)]
  | 27 => some [(1,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(4,3)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(6,4)]
  | 54 => some [(1,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(0,3)]
  | 64 => some [(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2)]
  | 72 => some [(5,3)]
  | 73 => some [(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(1,4),(3,4),(7,4)]
  | 80 => some [(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(2,1),(2,3),(2,5)]
  | 86 => some [(0,2),(6,0)]
  | 87 => some [(1,1),(7,1)]
  | 88 => some [(4,1),(7,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root5Node43Domains0_fast_eq : root5Node43Domains0 = expandDomains root5Node43Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node43Domains0 v = expandDomains root5Node43Domains0Fast v from by decide) v
def root5Node43Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(4,2)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(7,4)]
  | 13 => [(8,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(3,5)]
  | 18 => [(0,3)]
  | 19 => [(4,1)]
  | 20 => [(0,2)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(2,4)]
  | 27 => [(1,3)]
  | 28 => [(5,2)]
  | 29 => [(8,0)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(1,4)]
  | 40 => [(1,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(4,3)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(0,4)]
  | 52 => [(5,4)]
  | 53 => [(6,4)]
  | 54 => [(1,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(4,3)]
  | 62 => [(7,5)]
  | 63 => [(0,3)]
  | 64 => [(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(1,3)]
  | 71 => [(4,2)]
  | 72 => [(5,3)]
  | 73 => [(5,5),(8,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(1,4),(3,4)]
  | 80 => [(0,5),(6,3)]
  | 81 => [(4,4),(7,2)]
  | 82 => [(1,4),(7,4)]
  | 83 => [(0,5),(6,3)]
  | 84 => [(4,4),(7,2)]
  | 85 => [(2,3),(2,5)]
  | 86 => [(0,2),(6,0)]
  | 87 => [(1,1),(7,1)]
  | 88 => [(4,1),(7,5)]
  | 89 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root5Node43Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(3,5)]
  | 18 => some [(0,3)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,4)]
  | 27 => some [(1,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(4,3)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(6,4)]
  | 54 => some [(1,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(0,3)]
  | 64 => some [(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(4,2)]
  | 72 => some [(5,3)]
  | 73 => some [(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(1,4),(3,4)]
  | 80 => some [(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(2,3),(2,5)]
  | 86 => some [(0,2),(6,0)]
  | 87 => some [(1,1),(7,1)]
  | 88 => some [(4,1),(7,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root5Node43Domains1_fast_eq : root5Node43Domains1 = expandDomains root5Node43Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node43Domains1 v = expandDomains root5Node43Domains1Fast v from by decide) v
theorem root5Node43Step1Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Narrowing_checked :
    checkNarrowing table51 root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root5Node43Domains0 root5Node43Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node43Step1Chunk0_0_checked, root5Node43Step1Chunk0_1_checked, root5Node43Step1Chunk0_2_checked, root5Node43Step1Chunk0_3_checked, root5Node43Step1Chunk0_4_checked, root5Node43Step1Chunk0_5_checked, root5Node43Step1Chunk1_0_checked, root5Node43Step1Chunk1_1_checked, root5Node43Step1Chunk1_2_checked, root5Node43Step1Chunk1_3_checked, root5Node43Step1Chunk1_4_checked, root5Node43Step1Chunk1_5_checked, root5Node43Step1Chunk2_0_checked, root5Node43Step1Chunk2_1_checked, root5Node43Step1Chunk2_2_checked, root5Node43Step1Chunk2_3_checked, root5Node43Step1Chunk2_4_checked, root5Node43Step1Chunk2_5_checked, root5Node43Step1Chunk3_0_checked, root5Node43Step1Chunk3_1_checked, root5Node43Step1Chunk3_2_checked, root5Node43Step1Chunk3_3_checked, root5Node43Step1Chunk3_4_checked, root5Node43Step1Chunk3_5_checked, root5Node43Step1Chunk4_0_checked, root5Node43Step1Chunk4_1_checked, root5Node43Step1Chunk4_2_checked, root5Node43Step1Chunk4_3_checked, root5Node43Step1Chunk4_4_checked, root5Node43Step1Chunk4_5_checked, root5Node43Step1Chunk5_0_checked, root5Node43Step1Chunk5_1_checked, root5Node43Step1Chunk5_2_checked, root5Node43Step1Chunk5_3_checked, root5Node43Step1Chunk5_4_checked, root5Node43Step1Chunk5_5_checked, root5Node43Step1Chunk6_0_checked, root5Node43Step1Chunk6_1_checked, root5Node43Step1Chunk6_2_checked, root5Node43Step1Chunk6_3_checked, root5Node43Step1Chunk6_4_checked, root5Node43Step1Chunk6_5_checked, root5Node43Step1Chunk7_0_checked, root5Node43Step1Chunk7_1_checked, root5Node43Step1Chunk7_2_checked, root5Node43Step1Chunk7_3_checked, root5Node43Step1Chunk7_4_checked, root5Node43Step1Chunk7_5_checked, root5Node43Step1Chunk8_0_checked, root5Node43Step1Chunk8_1_checked, root5Node43Step1Chunk8_2_checked, root5Node43Step1Chunk8_3_checked, root5Node43Step1Chunk8_4_checked, root5Node43Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node43Step1_checked :
    checkReplacement table51 root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq
    root5Node43Step1Narrowing_checked (by decide)
def root5Node44Domains0 : Domains 91 State := restrict root5Node43Domains1 73 (5,5)
def root5Node44Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(3,5)]
  | 18 => some [(0,3)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,4)]
  | 27 => some [(1,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(4,3)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(6,4)]
  | 54 => some [(1,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(0,3)]
  | 64 => some [(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(4,2)]
  | 72 => some [(5,3)]
  | 73 => some [(5,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(1,4),(3,4)]
  | 80 => some [(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(2,3),(2,5)]
  | 86 => some [(0,2),(6,0)]
  | 87 => some [(1,1),(7,1)]
  | 88 => some [(4,1),(7,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root5Node44Domains0_fast_eq : root5Node44Domains0 = expandDomains root5Node44Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node44Domains0 v = expandDomains root5Node44Domains0Fast v from by decide) v
def root5Node44Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(4,2)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(7,4)]
  | 13 => [(8,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(3,5)]
  | 18 => [(0,3)]
  | 19 => [(4,1)]
  | 20 => [(0,2)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(2,4)]
  | 27 => [(1,3)]
  | 28 => [(5,2)]
  | 29 => [(8,0)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(1,4)]
  | 40 => [(1,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(4,3)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(0,4)]
  | 52 => [(5,4)]
  | 53 => [(6,4)]
  | 54 => [(1,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(4,3)]
  | 62 => [(7,5)]
  | 63 => [(0,3)]
  | 64 => [(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(1,3)]
  | 71 => [(4,2)]
  | 72 => [(5,3)]
  | 73 => [(5,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(5,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(1,4)]
  | 80 => [(0,5)]
  | 81 => [(4,4)]
  | 82 => [(1,4)]
  | 83 => [(0,5)]
  | 84 => [(4,4)]
  | 85 => [(2,5)]
  | 86 => [(6,0)]
  | 87 => [(7,1)]
  | 88 => [(7,5)]
  | 89 => [(6,0)]
  | _ => [(7,1)]
def root5Node44Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(3,5)]
  | 18 => some [(0,3)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,4)]
  | 27 => some [(1,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(4,3)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(6,4)]
  | 54 => some [(1,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(0,3)]
  | 64 => some [(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(4,2)]
  | 72 => some [(5,3)]
  | 73 => some [(5,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(1,4)]
  | 80 => some [(0,5)]
  | 81 => some [(4,4)]
  | 82 => some [(1,4)]
  | 83 => some [(0,5)]
  | 84 => some [(4,4)]
  | 85 => some [(2,5)]
  | 86 => some [(6,0)]
  | 87 => some [(7,1)]
  | 88 => some [(7,5)]
  | 89 => some [(6,0)]
  | _ => some [(7,1)]
theorem root5Node44Domains1_fast_eq : root5Node44Domains1 = expandDomains root5Node44Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node44Domains1 v = expandDomains root5Node44Domains1Fast v from by decide) v
theorem root5Node44Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Narrowing_checked :
    checkNarrowing table65 root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root5Node44Domains0 root5Node44Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node44Step1Chunk0_0_checked, root5Node44Step1Chunk0_1_checked, root5Node44Step1Chunk0_2_checked, root5Node44Step1Chunk0_3_checked, root5Node44Step1Chunk0_4_checked, root5Node44Step1Chunk0_5_checked, root5Node44Step1Chunk1_0_checked, root5Node44Step1Chunk1_1_checked, root5Node44Step1Chunk1_2_checked, root5Node44Step1Chunk1_3_checked, root5Node44Step1Chunk1_4_checked, root5Node44Step1Chunk1_5_checked, root5Node44Step1Chunk2_0_checked, root5Node44Step1Chunk2_1_checked, root5Node44Step1Chunk2_2_checked, root5Node44Step1Chunk2_3_checked, root5Node44Step1Chunk2_4_checked, root5Node44Step1Chunk2_5_checked, root5Node44Step1Chunk3_0_checked, root5Node44Step1Chunk3_1_checked, root5Node44Step1Chunk3_2_checked, root5Node44Step1Chunk3_3_checked, root5Node44Step1Chunk3_4_checked, root5Node44Step1Chunk3_5_checked, root5Node44Step1Chunk4_0_checked, root5Node44Step1Chunk4_1_checked, root5Node44Step1Chunk4_2_checked, root5Node44Step1Chunk4_3_checked, root5Node44Step1Chunk4_4_checked, root5Node44Step1Chunk4_5_checked, root5Node44Step1Chunk5_0_checked, root5Node44Step1Chunk5_1_checked, root5Node44Step1Chunk5_2_checked, root5Node44Step1Chunk5_3_checked, root5Node44Step1Chunk5_4_checked, root5Node44Step1Chunk5_5_checked, root5Node44Step1Chunk6_0_checked, root5Node44Step1Chunk6_1_checked, root5Node44Step1Chunk6_2_checked, root5Node44Step1Chunk6_3_checked, root5Node44Step1Chunk6_4_checked, root5Node44Step1Chunk6_5_checked, root5Node44Step1Chunk7_0_checked, root5Node44Step1Chunk7_1_checked, root5Node44Step1Chunk7_2_checked, root5Node44Step1Chunk7_3_checked, root5Node44Step1Chunk7_4_checked, root5Node44Step1Chunk7_5_checked, root5Node44Step1Chunk8_0_checked, root5Node44Step1Chunk8_1_checked, root5Node44Step1Chunk8_2_checked, root5Node44Step1Chunk8_3_checked, root5Node44Step1Chunk8_4_checked, root5Node44Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node44Step1_checked :
    checkReplacement table65 root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq
    root5Node44Step1Narrowing_checked (by decide)
theorem root5Node44Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node44Domains1 (.output 19) = true := by decide
def root5Node45Domains0 : Domains 91 State := restrict root5Node43Domains1 73 (8,5)
def root5Node45Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(3,5)]
  | 18 => some [(0,3)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,4)]
  | 27 => some [(1,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(4,3)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(6,4)]
  | 54 => some [(1,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(0,3)]
  | 64 => some [(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(4,2)]
  | 72 => some [(5,3)]
  | 73 => some [(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(1,4),(3,4)]
  | 80 => some [(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(2,3),(2,5)]
  | 86 => some [(0,2),(6,0)]
  | 87 => some [(1,1),(7,1)]
  | 88 => some [(4,1),(7,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root5Node45Domains0_fast_eq : root5Node45Domains0 = expandDomains root5Node45Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node45Domains0 v = expandDomains root5Node45Domains0Fast v from by decide) v
def root5Node45Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(4,2)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(7,4)]
  | 13 => [(8,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(3,5)]
  | 18 => [(0,3)]
  | 19 => [(4,1)]
  | 20 => [(0,2)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(2,4)]
  | 27 => [(1,3)]
  | 28 => [(5,2)]
  | 29 => [(8,0)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(1,4)]
  | 40 => [(1,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(4,3)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(0,4)]
  | 52 => [(5,4)]
  | 53 => [(6,4)]
  | 54 => [(1,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(4,3)]
  | 62 => [(7,5)]
  | 63 => [(0,3)]
  | 64 => [(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(1,3)]
  | 71 => [(4,2)]
  | 72 => [(5,3)]
  | 73 => [(8,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(3,4)]
  | 80 => [(6,3)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(2,3)]
  | 86 => [(0,2)]
  | 87 => [(1,1)]
  | 88 => [(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root5Node45Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(3,5)]
  | 18 => some [(0,3)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,4)]
  | 27 => some [(1,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(1,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(4,3)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(6,4)]
  | 54 => some [(1,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(0,3)]
  | 64 => some [(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(4,2)]
  | 72 => some [(5,3)]
  | 73 => some [(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(3,4)]
  | 80 => some [(6,3)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(2,3)]
  | 86 => some [(0,2)]
  | 87 => some [(1,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root5Node45Domains1_fast_eq : root5Node45Domains1 = expandDomains root5Node45Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node45Domains1 v = expandDomains root5Node45Domains1Fast v from by decide) v
theorem root5Node45Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Narrowing_checked :
    checkNarrowing table65 root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root5Node45Domains0 root5Node45Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node45Step1Chunk0_0_checked, root5Node45Step1Chunk0_1_checked, root5Node45Step1Chunk0_2_checked, root5Node45Step1Chunk0_3_checked, root5Node45Step1Chunk0_4_checked, root5Node45Step1Chunk0_5_checked, root5Node45Step1Chunk1_0_checked, root5Node45Step1Chunk1_1_checked, root5Node45Step1Chunk1_2_checked, root5Node45Step1Chunk1_3_checked, root5Node45Step1Chunk1_4_checked, root5Node45Step1Chunk1_5_checked, root5Node45Step1Chunk2_0_checked, root5Node45Step1Chunk2_1_checked, root5Node45Step1Chunk2_2_checked, root5Node45Step1Chunk2_3_checked, root5Node45Step1Chunk2_4_checked, root5Node45Step1Chunk2_5_checked, root5Node45Step1Chunk3_0_checked, root5Node45Step1Chunk3_1_checked, root5Node45Step1Chunk3_2_checked, root5Node45Step1Chunk3_3_checked, root5Node45Step1Chunk3_4_checked, root5Node45Step1Chunk3_5_checked, root5Node45Step1Chunk4_0_checked, root5Node45Step1Chunk4_1_checked, root5Node45Step1Chunk4_2_checked, root5Node45Step1Chunk4_3_checked, root5Node45Step1Chunk4_4_checked, root5Node45Step1Chunk4_5_checked, root5Node45Step1Chunk5_0_checked, root5Node45Step1Chunk5_1_checked, root5Node45Step1Chunk5_2_checked, root5Node45Step1Chunk5_3_checked, root5Node45Step1Chunk5_4_checked, root5Node45Step1Chunk5_5_checked, root5Node45Step1Chunk6_0_checked, root5Node45Step1Chunk6_1_checked, root5Node45Step1Chunk6_2_checked, root5Node45Step1Chunk6_3_checked, root5Node45Step1Chunk6_4_checked, root5Node45Step1Chunk6_5_checked, root5Node45Step1Chunk7_0_checked, root5Node45Step1Chunk7_1_checked, root5Node45Step1Chunk7_2_checked, root5Node45Step1Chunk7_3_checked, root5Node45Step1Chunk7_4_checked, root5Node45Step1Chunk7_5_checked, root5Node45Step1Chunk8_0_checked, root5Node45Step1Chunk8_1_checked, root5Node45Step1Chunk8_2_checked, root5Node45Step1Chunk8_3_checked, root5Node45Step1Chunk8_4_checked, root5Node45Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node45Step1_checked :
    checkReplacement table65 root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq
    root5Node45Step1Narrowing_checked (by decide)
theorem root5Node45Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node45Domains1 (.output 20) = true := by decide
def root5Node46Domains0 : Domains 91 State := restrict root5Node42Domains1 40 (7,3)
def root5Node46Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(3,5)]
  | 18 => some [(0,3)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,4)]
  | 27 => some [(1,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(1,4)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(4,3)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(0,4),(6,2)]
  | 52 => some [(5,4),(8,4)]
  | 53 => some [(6,4)]
  | 54 => some [(1,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(4,3),(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(0,3)]
  | 64 => some [(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3),(7,3)]
  | 71 => some [(4,2)]
  | 72 => some [(5,3)]
  | 73 => some [(5,5),(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(6,2)]
  | 79 => some [(1,4),(3,4),(7,4)]
  | 80 => some [(0,5),(6,3)]
  | 81 => some [(4,4),(7,2)]
  | 82 => some [(1,4),(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(2,1),(2,3),(2,5)]
  | 86 => some [(0,2),(6,0)]
  | 87 => some [(1,1),(7,1)]
  | 88 => some [(4,1),(7,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root5Node46Domains0_fast_eq : root5Node46Domains0 = expandDomains root5Node46Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node46Domains0 v = expandDomains root5Node46Domains0Fast v from by decide) v
def root5Node46Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(4,2)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(7,4)]
  | 13 => [(8,3)]
  | 14 => [(5,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(3,5)]
  | 18 => [(0,3)]
  | 19 => [(4,1)]
  | 20 => [(0,2)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(2,4)]
  | 27 => [(1,3)]
  | 28 => [(5,2)]
  | 29 => [(8,0)]
  | 30 => [(7,5)]
  | 31 => [(6,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(1,4)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(4,3)]
  | 49 => [(7,5)]
  | 50 => [(6,0)]
  | 51 => [(6,2)]
  | 52 => [(8,4)]
  | 53 => [(6,4)]
  | 54 => [(1,2)]
  | 55 => [(8,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(7,1)]
  | 62 => [(7,5)]
  | 63 => [(0,3)]
  | 64 => [(8,1)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(7,3)]
  | 71 => [(4,2)]
  | 72 => [(5,3)]
  | 73 => [(8,5)]
  | 74 => [(7,0)]
  | 75 => [(8,3)]
  | 76 => [(5,5),(8,5)]
  | 77 => [(7,0)]
  | 78 => [(6,2)]
  | 79 => [(7,4)]
  | 80 => [(6,3)]
  | 81 => [(7,2)]
  | 82 => [(7,4)]
  | 83 => [(0,5),(6,3)]
  | 84 => [(4,4),(7,2)]
  | 85 => [(2,1)]
  | 86 => [(0,2)]
  | 87 => [(1,1)]
  | 88 => [(4,1)]
  | 89 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root5Node46Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(4,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(7,4)]
  | 13 => some [(8,3)]
  | 14 => some [(5,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(3,5)]
  | 18 => some [(0,3)]
  | 19 => some [(4,1)]
  | 20 => some [(0,2)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(2,4)]
  | 27 => some [(1,3)]
  | 28 => some [(5,2)]
  | 29 => some [(8,0)]
  | 30 => some [(7,5)]
  | 31 => some [(6,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(1,4)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(4,3)]
  | 49 => some [(7,5)]
  | 50 => some [(6,0)]
  | 51 => some [(6,2)]
  | 52 => some [(8,4)]
  | 53 => some [(6,4)]
  | 54 => some [(1,2)]
  | 55 => some [(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(7,1)]
  | 62 => some [(7,5)]
  | 63 => some [(0,3)]
  | 64 => some [(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(7,3)]
  | 71 => some [(4,2)]
  | 72 => some [(5,3)]
  | 73 => some [(8,5)]
  | 74 => some [(7,0)]
  | 75 => some [(8,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,2)]
  | 79 => some [(7,4)]
  | 80 => some [(6,3)]
  | 81 => some [(7,2)]
  | 82 => some [(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(2,1)]
  | 86 => some [(0,2)]
  | 87 => some [(1,1)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root5Node46Domains1_fast_eq : root5Node46Domains1 = expandDomains root5Node46Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node46Domains1 v = expandDomains root5Node46Domains1Fast v from by decide) v
theorem root5Node46Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq (by decide)
theorem root5Node46Step1Narrowing_checked :
    checkNarrowing table54 root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root5Node46Domains0 root5Node46Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node46Step1Chunk0_0_checked, root5Node46Step1Chunk0_1_checked, root5Node46Step1Chunk0_2_checked, root5Node46Step1Chunk0_3_checked, root5Node46Step1Chunk0_4_checked, root5Node46Step1Chunk0_5_checked, root5Node46Step1Chunk1_0_checked, root5Node46Step1Chunk1_1_checked, root5Node46Step1Chunk1_2_checked, root5Node46Step1Chunk1_3_checked, root5Node46Step1Chunk1_4_checked, root5Node46Step1Chunk1_5_checked, root5Node46Step1Chunk2_0_checked, root5Node46Step1Chunk2_1_checked, root5Node46Step1Chunk2_2_checked, root5Node46Step1Chunk2_3_checked, root5Node46Step1Chunk2_4_checked, root5Node46Step1Chunk2_5_checked, root5Node46Step1Chunk3_0_checked, root5Node46Step1Chunk3_1_checked, root5Node46Step1Chunk3_2_checked, root5Node46Step1Chunk3_3_checked, root5Node46Step1Chunk3_4_checked, root5Node46Step1Chunk3_5_checked, root5Node46Step1Chunk4_0_checked, root5Node46Step1Chunk4_1_checked, root5Node46Step1Chunk4_2_checked, root5Node46Step1Chunk4_3_checked, root5Node46Step1Chunk4_4_checked, root5Node46Step1Chunk4_5_checked, root5Node46Step1Chunk5_0_checked, root5Node46Step1Chunk5_1_checked, root5Node46Step1Chunk5_2_checked, root5Node46Step1Chunk5_3_checked, root5Node46Step1Chunk5_4_checked, root5Node46Step1Chunk5_5_checked, root5Node46Step1Chunk6_0_checked, root5Node46Step1Chunk6_1_checked, root5Node46Step1Chunk6_2_checked, root5Node46Step1Chunk6_3_checked, root5Node46Step1Chunk6_4_checked, root5Node46Step1Chunk6_5_checked, root5Node46Step1Chunk7_0_checked, root5Node46Step1Chunk7_1_checked, root5Node46Step1Chunk7_2_checked, root5Node46Step1Chunk7_3_checked, root5Node46Step1Chunk7_4_checked, root5Node46Step1Chunk7_5_checked, root5Node46Step1Chunk8_0_checked, root5Node46Step1Chunk8_1_checked, root5Node46Step1Chunk8_2_checked, root5Node46Step1Chunk8_3_checked, root5Node46Step1Chunk8_4_checked, root5Node46Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node46Step1_checked :
    checkReplacement table54 root5Node46Domains0 root5Node46Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node46Domains0 root5Node46Domains1
    root5Node46Domains0Fast root5Node46Domains1Fast
    root5Node46Domains0_fast_eq root5Node46Domains1_fast_eq
    root5Node46Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
