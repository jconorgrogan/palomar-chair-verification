module

public import SpectreFinite.RadiusFiveRoot7Part80
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node205Domains0 : Domains 91 State := restrict root7Node204Domains1 83 (1,3)
def root7Node205Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(4,3)]
  | 86 => some [(3,5),(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(4,1),(8,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root7Node205Domains0_fast_eq : root7Node205Domains0 = expandDomains root7Node205Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node205Domains0 v = expandDomains root7Node205Domains0Fast v from by decide) v
def root7Node205Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(8,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,4)]
  | 52 => [(5,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(5,2)]
  | 61 => [(4,3)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(7,4)]
  | 83 => [(1,3)]
  | 84 => [(8,2)]
  | 85 => [(4,3)]
  | 86 => [(7,5)]
  | 87 => [(0,3)]
  | 88 => [(8,1)]
  | 89 => [(6,5)]
  | _ => [(0,4)]
def root7Node205Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(7,4)]
  | 83 => some [(1,3)]
  | 84 => some [(8,2)]
  | 85 => some [(4,3)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(8,1)]
  | 89 => some [(6,5)]
  | _ => some [(0,4)]
theorem root7Node205Domains1_fast_eq : root7Node205Domains1 = expandDomains root7Node205Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node205Domains1 v = expandDomains root7Node205Domains1Fast v from by decide) v
theorem root7Node205Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq (by decide)
theorem root7Node205Step1Narrowing_checked :
    checkNarrowing table56 root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node205Domains0 root7Node205Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node205Step1Chunk0_0_checked, root7Node205Step1Chunk0_1_checked, root7Node205Step1Chunk0_2_checked, root7Node205Step1Chunk0_3_checked, root7Node205Step1Chunk0_4_checked, root7Node205Step1Chunk0_5_checked, root7Node205Step1Chunk1_0_checked, root7Node205Step1Chunk1_1_checked, root7Node205Step1Chunk1_2_checked, root7Node205Step1Chunk1_3_checked, root7Node205Step1Chunk1_4_checked, root7Node205Step1Chunk1_5_checked, root7Node205Step1Chunk2_0_checked, root7Node205Step1Chunk2_1_checked, root7Node205Step1Chunk2_2_checked, root7Node205Step1Chunk2_3_checked, root7Node205Step1Chunk2_4_checked, root7Node205Step1Chunk2_5_checked, root7Node205Step1Chunk3_0_checked, root7Node205Step1Chunk3_1_checked, root7Node205Step1Chunk3_2_checked, root7Node205Step1Chunk3_3_checked, root7Node205Step1Chunk3_4_checked, root7Node205Step1Chunk3_5_checked, root7Node205Step1Chunk4_0_checked, root7Node205Step1Chunk4_1_checked, root7Node205Step1Chunk4_2_checked, root7Node205Step1Chunk4_3_checked, root7Node205Step1Chunk4_4_checked, root7Node205Step1Chunk4_5_checked, root7Node205Step1Chunk5_0_checked, root7Node205Step1Chunk5_1_checked, root7Node205Step1Chunk5_2_checked, root7Node205Step1Chunk5_3_checked, root7Node205Step1Chunk5_4_checked, root7Node205Step1Chunk5_5_checked, root7Node205Step1Chunk6_0_checked, root7Node205Step1Chunk6_1_checked, root7Node205Step1Chunk6_2_checked, root7Node205Step1Chunk6_3_checked, root7Node205Step1Chunk6_4_checked, root7Node205Step1Chunk6_5_checked, root7Node205Step1Chunk7_0_checked, root7Node205Step1Chunk7_1_checked, root7Node205Step1Chunk7_2_checked, root7Node205Step1Chunk7_3_checked, root7Node205Step1Chunk7_4_checked, root7Node205Step1Chunk7_5_checked, root7Node205Step1Chunk8_0_checked, root7Node205Step1Chunk8_1_checked, root7Node205Step1Chunk8_2_checked, root7Node205Step1Chunk8_3_checked, root7Node205Step1Chunk8_4_checked, root7Node205Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node205Step1_checked :
    checkReplacement table56 root7Node205Domains0 root7Node205Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node205Domains0 root7Node205Domains1
    root7Node205Domains0Fast root7Node205Domains1Fast
    root7Node205Domains0_fast_eq root7Node205Domains1_fast_eq
    root7Node205Step1Narrowing_checked (by decide)
theorem root7Node205Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node205Domains1 (.output 101) = true := by decide
def root7Node206Domains0 : Domains 91 State := restrict root7Node204Domains1 83 (6,3)
def root7Node206Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2),(8,2)]
  | 85 => some [(4,3)]
  | 86 => some [(3,5),(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(4,1),(8,1)]
  | 89 => some [(0,2),(6,5)]
  | _ => some [(0,4),(1,1)]
theorem root7Node206Domains0_fast_eq : root7Node206Domains0 = expandDomains root7Node206Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node206Domains0 v = expandDomains root7Node206Domains0Fast v from by decide) v
def root7Node206Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(8,0)]
  | 4 => [(7,3)]
  | 5 => [(8,2)]
  | 6 => [(8,1)]
  | 7 => [(6,5)]
  | 8 => [(0,4)]
  | 9 => [(5,4)]
  | 10 => [(6,4)]
  | 11 => [(1,2)]
  | 12 => [(8,4)]
  | 13 => [(5,3)]
  | 14 => [(8,5)]
  | 15 => [(7,0)]
  | 16 => [(4,3)]
  | 17 => [(7,5)]
  | 18 => [(0,3)]
  | 19 => [(8,1)]
  | 20 => [(1,5)]
  | 21 => [(7,4)]
  | 22 => [(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(1,3)]
  | 26 => [(4,2)]
  | 27 => [(5,3)]
  | 28 => [(8,5)]
  | 29 => [(7,0)]
  | 30 => [(4,1)]
  | 31 => [(0,2)]
  | 32 => [(1,1)]
  | 33 => [(8,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(3,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(5,2)]
  | 42 => [(8,0)]
  | 43 => [(8,3)]
  | 44 => [(5,5)]
  | 45 => [(7,0)]
  | 46 => [(2,3)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(4,1)]
  | 50 => [(0,2)]
  | 51 => [(0,4)]
  | 52 => [(5,4)]
  | 53 => [(1,4)]
  | 54 => [(0,5)]
  | 55 => [(4,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(4,0)]
  | 59 => [(7,3)]
  | 60 => [(5,2)]
  | 61 => [(4,3)]
  | 62 => [(7,5)]
  | 63 => [(6,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(5,1)]
  | 68 => [(0,1)]
  | 69 => [(6,2)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(1,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3)]
  | 86 => [(3,5),(7,5)]
  | 87 => [(0,3)]
  | 88 => [(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root7Node206Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(3,5),(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root7Node206Domains1_fast_eq : root7Node206Domains1 = expandDomains root7Node206Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node206Domains1 v = expandDomains root7Node206Domains1Fast v from by decide) v
theorem root7Node206Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq (by decide)
theorem root7Node206Step1Narrowing_checked :
    checkNarrowing table56 root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node206Domains0 root7Node206Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node206Step1Chunk0_0_checked, root7Node206Step1Chunk0_1_checked, root7Node206Step1Chunk0_2_checked, root7Node206Step1Chunk0_3_checked, root7Node206Step1Chunk0_4_checked, root7Node206Step1Chunk0_5_checked, root7Node206Step1Chunk1_0_checked, root7Node206Step1Chunk1_1_checked, root7Node206Step1Chunk1_2_checked, root7Node206Step1Chunk1_3_checked, root7Node206Step1Chunk1_4_checked, root7Node206Step1Chunk1_5_checked, root7Node206Step1Chunk2_0_checked, root7Node206Step1Chunk2_1_checked, root7Node206Step1Chunk2_2_checked, root7Node206Step1Chunk2_3_checked, root7Node206Step1Chunk2_4_checked, root7Node206Step1Chunk2_5_checked, root7Node206Step1Chunk3_0_checked, root7Node206Step1Chunk3_1_checked, root7Node206Step1Chunk3_2_checked, root7Node206Step1Chunk3_3_checked, root7Node206Step1Chunk3_4_checked, root7Node206Step1Chunk3_5_checked, root7Node206Step1Chunk4_0_checked, root7Node206Step1Chunk4_1_checked, root7Node206Step1Chunk4_2_checked, root7Node206Step1Chunk4_3_checked, root7Node206Step1Chunk4_4_checked, root7Node206Step1Chunk4_5_checked, root7Node206Step1Chunk5_0_checked, root7Node206Step1Chunk5_1_checked, root7Node206Step1Chunk5_2_checked, root7Node206Step1Chunk5_3_checked, root7Node206Step1Chunk5_4_checked, root7Node206Step1Chunk5_5_checked, root7Node206Step1Chunk6_0_checked, root7Node206Step1Chunk6_1_checked, root7Node206Step1Chunk6_2_checked, root7Node206Step1Chunk6_3_checked, root7Node206Step1Chunk6_4_checked, root7Node206Step1Chunk6_5_checked, root7Node206Step1Chunk7_0_checked, root7Node206Step1Chunk7_1_checked, root7Node206Step1Chunk7_2_checked, root7Node206Step1Chunk7_3_checked, root7Node206Step1Chunk7_4_checked, root7Node206Step1Chunk7_5_checked, root7Node206Step1Chunk8_0_checked, root7Node206Step1Chunk8_1_checked, root7Node206Step1Chunk8_2_checked, root7Node206Step1Chunk8_3_checked, root7Node206Step1Chunk8_4_checked, root7Node206Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node206Step1_checked :
    checkReplacement table56 root7Node206Domains0 root7Node206Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node206Domains0 root7Node206Domains1
    root7Node206Domains0Fast root7Node206Domains1Fast
    root7Node206Domains0_fast_eq root7Node206Domains1_fast_eq
    root7Node206Step1Narrowing_checked (by decide)
def root7Node207Domains0 : Domains 91 State := restrict root7Node206Domains1 86 (3,5)
def root7Node207Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(3,5)]
  | 87 => some [(0,3)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root7Node207Domains0_fast_eq : root7Node207Domains0 = expandDomains root7Node207Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node207Domains0 v = expandDomains root7Node207Domains0Fast v from by decide) v
theorem root7Node207Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node207Domains0 (.output 102) = true := by decide
def root7Node208Domains0 : Domains 91 State := restrict root7Node206Domains1 86 (7,5)
def root7Node208Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(8,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(8,1)]
  | 7 => some [(6,5)]
  | 8 => some [(0,4)]
  | 9 => some [(5,4)]
  | 10 => some [(6,4)]
  | 11 => some [(1,2)]
  | 12 => some [(8,4)]
  | 13 => some [(5,3)]
  | 14 => some [(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(4,3)]
  | 17 => some [(7,5)]
  | 18 => some [(0,3)]
  | 19 => some [(8,1)]
  | 20 => some [(1,5)]
  | 21 => some [(7,4)]
  | 22 => some [(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(1,3)]
  | 26 => some [(4,2)]
  | 27 => some [(5,3)]
  | 28 => some [(8,5)]
  | 29 => some [(7,0)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(8,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(3,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(5,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,3)]
  | 44 => some [(5,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(4,1)]
  | 50 => some [(0,2)]
  | 51 => some [(0,4)]
  | 52 => some [(5,4)]
  | 53 => some [(1,4)]
  | 54 => some [(0,5)]
  | 55 => some [(4,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(4,0)]
  | 59 => some [(7,3)]
  | 60 => some [(5,2)]
  | 61 => some [(4,3)]
  | 62 => some [(7,5)]
  | 63 => some [(6,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(5,1)]
  | 68 => some [(0,1)]
  | 69 => some [(6,2)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(1,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(7,5)]
  | 87 => some [(0,3)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root7Node208Domains0_fast_eq : root7Node208Domains0 = expandDomains root7Node208Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node208Domains0 v = expandDomains root7Node208Domains0Fast v from by decide) v
theorem root7Node208Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node208Domains0 (.output 103) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
