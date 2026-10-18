module

public import SpectreFinite.RadiusThreeRoot7Part26
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable17

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node41Domains0 : Domains 37 State := restrict root7Node40Domains3 22 (3,4)
def root7Node41Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(7,0)]
  | 22 => some [(3,4)]
  | 23 => some [(6,3)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(6,3)]
  | 27 => some [(7,2)]
  | 28 => some [(0,2)]
  | 29 => some [(1,1)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(5,2)]
  | _ => some [(8,0)]
theorem root7Node41Domains0_fast_eq : root7Node41Domains0 = expandDomains root7Node41Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node41Domains0 v = expandDomains root7Node41Domains0Fast v from by decide) v
theorem root7Node41Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node41Domains0 (.output 19) = true := by decide
def root7Node42Domains0 : Domains 37 State := restrict root7Node40Domains3 22 (7,4)
def root7Node42Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3)]
  | 10 => some [(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(8,1)]
  | 14 => some [(6,5)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(7,0)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(6,3)]
  | 27 => some [(7,2)]
  | 28 => some [(0,2)]
  | 29 => some [(1,1)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2)]
  | 32 => some [(1,1)]
  | 33 => some [(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(5,2)]
  | _ => some [(8,0)]
theorem root7Node42Domains0_fast_eq : root7Node42Domains0 = expandDomains root7Node42Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node42Domains0 v = expandDomains root7Node42Domains0Fast v from by decide) v
theorem root7Node42Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node42Domains0 (.output 20) = true := by decide
def root7Node43Domains0 : Domains 37 State := restrict root7Node33Domains2 4 (6,2)
def root7Node43Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(6,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(0,3),(1,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1),(8,1)]
  | 14 => some [(0,2),(6,5)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3)]
  | 17 => some [(4,5),(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(7,3),(8,3)]
  | 20 => some [(5,2),(5,5),(8,5)]
  | 21 => some [(3,0),(5,0),(7,0)]
  | 22 => some [(1,4),(3,4),(5,4),(7,4)]
  | 23 => some [(0,0),(0,5),(6,3)]
  | 24 => some [(4,4),(7,2)]
  | 25 => some [(1,4),(6,4),(7,4)]
  | 26 => some [(0,5),(1,2),(6,3)]
  | 27 => some [(4,4),(7,2),(8,4)]
  | 28 => some [(0,2),(1,5),(6,0)]
  | 29 => some [(1,1),(6,1),(7,1)]
  | 30 => some [(4,1),(7,5)]
  | 31 => some [(0,2),(0,3),(6,0)]
  | 32 => some [(1,1),(7,1),(8,1)]
  | 33 => some [(2,0),(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(5,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root7Node43Domains0_fast_eq : root7Node43Domains0 = expandDomains root7Node43Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node43Domains0 v = expandDomains root7Node43Domains0Fast v from by decide) v
def root7Node43Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0)]
  | 2 => [(4,5)]
  | 3 => [(7,0)]
  | 4 => [(6,2)]
  | 5 => [(8,4)]
  | 6 => [(0,0)]
  | 7 => [(7,2)]
  | 8 => [(7,4)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(1,5)]
  | 12 => [(6,1)]
  | 13 => [(4,1),(8,1)]
  | 14 => [(0,2),(6,5)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,2),(5,5),(8,5)]
  | 21 => [(3,0),(5,0),(7,0)]
  | 22 => [(5,4)]
  | 23 => [(0,0)]
  | 24 => [(7,2)]
  | 25 => [(7,4)]
  | 26 => [(0,5),(1,2),(6,3)]
  | 27 => [(4,4),(7,2),(8,4)]
  | 28 => [(1,5)]
  | 29 => [(6,1)]
  | 30 => [(4,1)]
  | 31 => [(0,2),(0,3),(6,0)]
  | 32 => [(1,1),(7,1),(8,1)]
  | 33 => [(2,0),(4,0)]
  | 34 => [(7,3)]
  | 35 => [(4,2),(5,2),(8,2)]
  | _ => [(5,0),(5,3),(8,0)]
def root7Node43Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0)]
  | 2 => some [(4,5)]
  | 3 => some [(7,0)]
  | 4 => some [(6,2)]
  | 5 => some [(8,4)]
  | 6 => some [(0,0)]
  | 7 => some [(7,2)]
  | 8 => some [(7,4)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,5)]
  | 12 => some [(6,1)]
  | 13 => some [(4,1),(8,1)]
  | 14 => some [(0,2),(6,5)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,2),(5,5),(8,5)]
  | 21 => some [(3,0),(5,0),(7,0)]
  | 22 => some [(5,4)]
  | 23 => some [(0,0)]
  | 24 => some [(7,2)]
  | 25 => some [(7,4)]
  | 26 => some [(0,5),(1,2),(6,3)]
  | 27 => some [(4,4),(7,2),(8,4)]
  | 28 => some [(1,5)]
  | 29 => some [(6,1)]
  | 30 => some [(4,1)]
  | 31 => some [(0,2),(0,3),(6,0)]
  | 32 => some [(1,1),(7,1),(8,1)]
  | 33 => some [(2,0),(4,0)]
  | 34 => some [(7,3)]
  | 35 => some [(4,2),(5,2),(8,2)]
  | _ => some [(5,0),(5,3),(8,0)]
theorem root7Node43Domains1_fast_eq : root7Node43Domains1 = expandDomains root7Node43Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root7Node43Domains1 v = expandDomains root7Node43Domains1Fast v from by decide) v
theorem root7Node43Step1Chunk0_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk0_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk0_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk0_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk0_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk0_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows0_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk1_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows1_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk2_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows2_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk3_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows3_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk4_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows4_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk5_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows5_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk6_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows6_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk7_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows7_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_0_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_0⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_1_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_1⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_2_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_2⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_3_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_3⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_4_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_4⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1Chunk8_5_checked :
    checkNarrowing ⟨table17Scope, table17Rows8_5⟩
      root7Node43Domains0 root7Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node43Domains0 root7Node43Domains1
    root7Node43Domains0Fast root7Node43Domains1Fast
    root7Node43Domains0_fast_eq root7Node43Domains1_fast_eq (by decide)
theorem root7Node43Step1_checked :
    checkReplacement table17 root7Node43Domains0 root7Node43Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node43Step1Chunk0_0_checked, root7Node43Step1Chunk0_1_checked, root7Node43Step1Chunk0_2_checked, root7Node43Step1Chunk0_3_checked, root7Node43Step1Chunk0_4_checked, root7Node43Step1Chunk0_5_checked, root7Node43Step1Chunk1_0_checked, root7Node43Step1Chunk1_1_checked, root7Node43Step1Chunk1_2_checked, root7Node43Step1Chunk1_3_checked, root7Node43Step1Chunk1_4_checked, root7Node43Step1Chunk1_5_checked, root7Node43Step1Chunk2_0_checked, root7Node43Step1Chunk2_1_checked, root7Node43Step1Chunk2_2_checked, root7Node43Step1Chunk2_3_checked, root7Node43Step1Chunk2_4_checked, root7Node43Step1Chunk2_5_checked, root7Node43Step1Chunk3_0_checked, root7Node43Step1Chunk3_1_checked, root7Node43Step1Chunk3_2_checked, root7Node43Step1Chunk3_3_checked, root7Node43Step1Chunk3_4_checked, root7Node43Step1Chunk3_5_checked, root7Node43Step1Chunk4_0_checked, root7Node43Step1Chunk4_1_checked, root7Node43Step1Chunk4_2_checked, root7Node43Step1Chunk4_3_checked, root7Node43Step1Chunk4_4_checked, root7Node43Step1Chunk4_5_checked, root7Node43Step1Chunk5_0_checked, root7Node43Step1Chunk5_1_checked, root7Node43Step1Chunk5_2_checked, root7Node43Step1Chunk5_3_checked, root7Node43Step1Chunk5_4_checked, root7Node43Step1Chunk5_5_checked, root7Node43Step1Chunk6_0_checked, root7Node43Step1Chunk6_1_checked, root7Node43Step1Chunk6_2_checked, root7Node43Step1Chunk6_3_checked, root7Node43Step1Chunk6_4_checked, root7Node43Step1Chunk6_5_checked, root7Node43Step1Chunk7_0_checked, root7Node43Step1Chunk7_1_checked, root7Node43Step1Chunk7_2_checked, root7Node43Step1Chunk7_3_checked, root7Node43Step1Chunk7_4_checked, root7Node43Step1Chunk7_5_checked, root7Node43Step1Chunk8_0_checked, root7Node43Step1Chunk8_1_checked, root7Node43Step1Chunk8_2_checked, root7Node43Step1Chunk8_3_checked, root7Node43Step1Chunk8_4_checked, root7Node43Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
