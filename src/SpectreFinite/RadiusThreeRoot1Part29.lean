module

public import SpectreFinite.RadiusThreeRoot1Part28
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable30

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node48Domains0 : Domains 37 State := restrict root1Node47Domains1 35 (3,5)
def root1Node48Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(6,5)]
  | 29 => some [(0,4)]
  | 30 => some [(5,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(3,5)]
  | _ => some [(0,3)]
theorem root1Node48Domains0_fast_eq : root1Node48Domains0 = expandDomains root1Node48Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node48Domains0 v = expandDomains root1Node48Domains0Fast v from by decide) v
theorem root1Node48Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node48Domains0 (.output 23) = true := by decide
def root1Node49Domains0 : Domains 37 State := restrict root1Node47Domains1 35 (7,5)
def root1Node49Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(8,2)]
  | 25 => some [(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(6,5)]
  | 29 => some [(0,4)]
  | 30 => some [(5,4)]
  | 31 => some [(6,4)]
  | 32 => some [(1,2)]
  | 33 => some [(7,0)]
  | 34 => some [(4,3)]
  | 35 => some [(7,5)]
  | _ => some [(0,3)]
theorem root1Node49Domains0_fast_eq : root1Node49Domains0 = expandDomains root1Node49Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node49Domains0 v = expandDomains root1Node49Domains0Fast v from by decide) v
theorem root1Node49Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node49Domains0 (.output 24) = true := by decide
def root1Node50Domains0 : Domains 37 State := restrict root1Node46Domains2 23 (6,3)
def root1Node50Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(7,2),(8,2)]
  | 25 => some [(4,0),(8,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(0,2),(6,5)]
  | 29 => some [(0,4),(1,1)]
  | 30 => some [(5,1),(5,4)]
  | 31 => some [(0,1),(6,4)]
  | 32 => some [(1,2),(6,2)]
  | 33 => some [(7,0),(8,0)]
  | 34 => some [(4,3),(8,3)]
  | 35 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root1Node50Domains0_fast_eq : root1Node50Domains0 = expandDomains root1Node50Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node50Domains0 v = expandDomains root1Node50Domains0Fast v from by decide) v
def root1Node50Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,2)]
  | 5 => [(4,0)]
  | 6 => [(7,3)]
  | 7 => [(8,2)]
  | 8 => [(8,0)]
  | 9 => [(6,1)]
  | 10 => [(5,1)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(8,4)]
  | 14 => [(6,4)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(0,3)]
  | 22 => [(7,4)]
  | 23 => [(6,3)]
  | 24 => [(7,2)]
  | 25 => [(4,0)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(0,2)]
  | 29 => [(1,1)]
  | 30 => [(5,1)]
  | 31 => [(0,1)]
  | 32 => [(6,2)]
  | 33 => [(8,0)]
  | 34 => [(8,3)]
  | 35 => [(5,5)]
  | _ => [(1,0)]
def root1Node50Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,2)]
  | 5 => some [(4,0)]
  | 6 => some [(7,3)]
  | 7 => some [(8,2)]
  | 8 => some [(8,0)]
  | 9 => some [(6,1)]
  | 10 => some [(5,1)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(8,4)]
  | 14 => some [(6,4)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(0,3)]
  | 22 => some [(7,4)]
  | 23 => some [(6,3)]
  | 24 => some [(7,2)]
  | 25 => some [(4,0)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(0,2)]
  | 29 => some [(1,1)]
  | 30 => some [(5,1)]
  | 31 => some [(0,1)]
  | 32 => some [(6,2)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(5,5)]
  | _ => some [(1,0)]
theorem root1Node50Domains1_fast_eq : root1Node50Domains1 = expandDomains root1Node50Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root1Node50Domains1 v = expandDomains root1Node50Domains1Fast v from by decide) v
theorem root1Node50Step1Chunk0_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk0_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk0_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk0_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk0_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk0_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows0_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk1_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows1_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk2_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows2_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk3_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows3_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk4_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows4_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk5_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows5_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk6_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows6_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk7_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows7_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_0_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_0⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_1_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_1⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_2_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_2⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_3_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_3⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_4_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_4⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1Chunk8_5_checked :
    checkNarrowing ⟨table30Scope, table30Rows8_5⟩
      root1Node50Domains0 root1Node50Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node50Domains0 root1Node50Domains1
    root1Node50Domains0Fast root1Node50Domains1Fast
    root1Node50Domains0_fast_eq root1Node50Domains1_fast_eq (by decide)
theorem root1Node50Step1_checked :
    checkReplacement table30 root1Node50Domains0 root1Node50Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node50Step1Chunk0_0_checked, root1Node50Step1Chunk0_1_checked, root1Node50Step1Chunk0_2_checked, root1Node50Step1Chunk0_3_checked, root1Node50Step1Chunk0_4_checked, root1Node50Step1Chunk0_5_checked, root1Node50Step1Chunk1_0_checked, root1Node50Step1Chunk1_1_checked, root1Node50Step1Chunk1_2_checked, root1Node50Step1Chunk1_3_checked, root1Node50Step1Chunk1_4_checked, root1Node50Step1Chunk1_5_checked, root1Node50Step1Chunk2_0_checked, root1Node50Step1Chunk2_1_checked, root1Node50Step1Chunk2_2_checked, root1Node50Step1Chunk2_3_checked, root1Node50Step1Chunk2_4_checked, root1Node50Step1Chunk2_5_checked, root1Node50Step1Chunk3_0_checked, root1Node50Step1Chunk3_1_checked, root1Node50Step1Chunk3_2_checked, root1Node50Step1Chunk3_3_checked, root1Node50Step1Chunk3_4_checked, root1Node50Step1Chunk3_5_checked, root1Node50Step1Chunk4_0_checked, root1Node50Step1Chunk4_1_checked, root1Node50Step1Chunk4_2_checked, root1Node50Step1Chunk4_3_checked, root1Node50Step1Chunk4_4_checked, root1Node50Step1Chunk4_5_checked, root1Node50Step1Chunk5_0_checked, root1Node50Step1Chunk5_1_checked, root1Node50Step1Chunk5_2_checked, root1Node50Step1Chunk5_3_checked, root1Node50Step1Chunk5_4_checked, root1Node50Step1Chunk5_5_checked, root1Node50Step1Chunk6_0_checked, root1Node50Step1Chunk6_1_checked, root1Node50Step1Chunk6_2_checked, root1Node50Step1Chunk6_3_checked, root1Node50Step1Chunk6_4_checked, root1Node50Step1Chunk6_5_checked, root1Node50Step1Chunk7_0_checked, root1Node50Step1Chunk7_1_checked, root1Node50Step1Chunk7_2_checked, root1Node50Step1Chunk7_3_checked, root1Node50Step1Chunk7_4_checked, root1Node50Step1Chunk7_5_checked, root1Node50Step1Chunk8_0_checked, root1Node50Step1Chunk8_1_checked, root1Node50Step1Chunk8_2_checked, root1Node50Step1Chunk8_3_checked, root1Node50Step1Chunk8_4_checked, root1Node50Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node50Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node50Domains1 (.output 25) = true := by decide
end SpectreFinite.HexSearch.RadiusThree
