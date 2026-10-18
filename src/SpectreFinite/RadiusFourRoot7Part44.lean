module

public import SpectreFinite.RadiusFourRoot7Part43
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable1
public import SpectreFinite.RadiusFourTable20
public import SpectreFinite.RadiusFourTable37

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node134Domains0 : Domains 61 State := restrict root7Node133Domains1 56 (5,4)
def root7Node134Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(3,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(7,0)]
  | 55 => some [(2,3)]
  | 56 => some [(5,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(6,4)]
theorem root7Node134Domains0_fast_eq : root7Node134Domains0 = expandDomains root7Node134Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node134Domains0 v = expandDomains root7Node134Domains0Fast v from by decide) v
theorem root7Node134Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node134Domains0 (.output 66) = true := by decide
def root7Node135Domains0 : Domains 61 State := restrict root7Node133Domains1 56 (8,4)
def root7Node135Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(3,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(7,0)]
  | 55 => some [(2,3)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(6,4)]
theorem root7Node135Domains0_fast_eq : root7Node135Domains0 = expandDomains root7Node135Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node135Domains0 v = expandDomains root7Node135Domains0Fast v from by decide) v
theorem root7Node135Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node135Domains0 (.output 67) = true := by decide
def root7Node136Domains0 : Domains 61 State := restrict root7Node92Domains4 2 (5,4)
def root7Node136Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5),(6,5),(7,5)]
  | 1 => some [(0,3),(0,4),(6,1)]
  | 2 => some [(5,4)]
  | 3 => some [(0,1),(1,4),(6,4)]
  | 4 => some [(0,5),(1,2),(6,2)]
  | 5 => some [(4,5),(7,3),(8,5)]
  | 6 => some [(4,2),(7,0)]
  | 7 => some [(4,3),(5,3),(8,3)]
  | 8 => some [(7,5),(8,5)]
  | 9 => some [(0,3),(1,0),(6,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(0,0),(6,3),(6,4)]
  | 12 => some [(1,2),(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3),(8,0)]
  | 17 => some [(4,5),(7,3),(8,5)]
  | 18 => some [(0,2),(1,5),(7,5)]
  | 19 => some [(0,3),(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(3,4),(5,4)]
  | 24 => some [(0,0),(6,3),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => some [(4,2),(7,0),(8,0)]
  | 28 => some [(5,3),(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3),(4,3)]
  | 32 => some [(0,2),(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(1,1),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => some [(1,4),(3,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(6,4),(7,4)]
  | 40 => some [(0,5),(1,2),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(0,3),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5),(8,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(6,3),(6,4)]
theorem root7Node136Domains0_fast_eq : root7Node136Domains0 = expandDomains root7Node136Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node136Domains0 v = expandDomains root7Node136Domains0Fast v from by decide) v
def root7Node136Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,1),(1,4),(6,4)]
  | 4 => [(0,5),(1,2),(6,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3),(1,0),(6,0)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2),(8,2)]
  | 16 => [(5,0),(5,3),(8,0)]
  | 17 => [(4,5),(7,3),(8,5)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(3,4),(5,4)]
  | 24 => [(0,0),(6,3),(6,4)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(4,5),(5,2),(5,5),(8,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(2,3),(4,3)]
  | 32 => [(0,2),(1,5),(3,5),(7,5)]
  | 33 => [(0,3),(1,1),(6,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(4,4),(5,4),(7,2),(8,4)]
  | 36 => [(1,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(6,4),(7,4)]
  | 40 => [(0,5),(1,2),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 42 => [(1,3),(3,3),(5,3),(7,3)]
  | 43 => [(4,1),(7,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(0,3),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(6,5)]
  | 50 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(4,2),(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(5,3),(7,0)]
  | 55 => [(2,3),(2,5),(4,5),(8,5)]
  | 56 => [(5,1),(5,4),(8,4)]
  | 57 => [(0,1),(1,4),(6,4)]
  | 58 => [(0,5),(1,2),(6,2)]
  | 59 => [(4,4),(7,4),(8,4)]
  | _ => [(0,0),(1,3),(6,3),(6,4)]
def root7Node136Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,1),(1,4),(6,4)]
  | 4 => some [(0,5),(1,2),(6,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3),(1,0),(6,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3),(8,0)]
  | 17 => some [(4,5),(7,3),(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(3,4),(5,4)]
  | 24 => some [(0,0),(6,3),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(8,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3),(4,3)]
  | 32 => some [(0,2),(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(1,1),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(5,4),(7,2),(8,4)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(6,4),(7,4)]
  | 40 => some [(0,5),(1,2),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(0,3),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5),(8,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(6,3),(6,4)]
theorem root7Node136Domains1_fast_eq : root7Node136Domains1 = expandDomains root7Node136Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node136Domains1 v = expandDomains root7Node136Domains1Fast v from by decide) v
theorem root7Node136Step1Chunk0_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_0⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk0_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_1⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk0_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_2⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk0_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_3⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk0_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_4⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk0_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_5⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk1_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_0⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk1_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_1⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk1_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_2⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk1_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_3⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk1_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_4⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk1_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_5⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk2_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_0⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk2_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_1⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk2_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_2⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk2_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_3⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk2_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_4⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk2_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_5⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk3_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_0⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk3_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_1⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk3_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_2⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk3_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_3⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk3_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_4⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk3_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_5⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk4_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_0⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk4_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_1⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk4_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_2⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk4_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_3⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk4_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_4⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk4_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_5⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk5_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_0⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk5_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_1⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk5_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_2⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk5_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_3⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk5_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_4⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk5_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_5⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk6_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_0⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk6_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_1⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk6_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_2⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk6_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_3⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk6_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_4⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk6_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_5⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk7_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_0⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk7_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_1⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk7_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_2⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk7_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_3⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk7_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_4⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk7_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_5⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk8_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_0⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk8_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_1⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk8_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_2⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk8_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_3⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk8_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_4⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1Chunk8_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_5⟩
      root7Node136Domains0 root7Node136Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains0 root7Node136Domains1
    root7Node136Domains0Fast root7Node136Domains1Fast
    root7Node136Domains0_fast_eq root7Node136Domains1_fast_eq (by decide)
theorem root7Node136Step1_checked :
    checkReplacement table20 root7Node136Domains0 root7Node136Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node136Step1Chunk0_0_checked, root7Node136Step1Chunk0_1_checked, root7Node136Step1Chunk0_2_checked, root7Node136Step1Chunk0_3_checked, root7Node136Step1Chunk0_4_checked, root7Node136Step1Chunk0_5_checked, root7Node136Step1Chunk1_0_checked, root7Node136Step1Chunk1_1_checked, root7Node136Step1Chunk1_2_checked, root7Node136Step1Chunk1_3_checked, root7Node136Step1Chunk1_4_checked, root7Node136Step1Chunk1_5_checked, root7Node136Step1Chunk2_0_checked, root7Node136Step1Chunk2_1_checked, root7Node136Step1Chunk2_2_checked, root7Node136Step1Chunk2_3_checked, root7Node136Step1Chunk2_4_checked, root7Node136Step1Chunk2_5_checked, root7Node136Step1Chunk3_0_checked, root7Node136Step1Chunk3_1_checked, root7Node136Step1Chunk3_2_checked, root7Node136Step1Chunk3_3_checked, root7Node136Step1Chunk3_4_checked, root7Node136Step1Chunk3_5_checked, root7Node136Step1Chunk4_0_checked, root7Node136Step1Chunk4_1_checked, root7Node136Step1Chunk4_2_checked, root7Node136Step1Chunk4_3_checked, root7Node136Step1Chunk4_4_checked, root7Node136Step1Chunk4_5_checked, root7Node136Step1Chunk5_0_checked, root7Node136Step1Chunk5_1_checked, root7Node136Step1Chunk5_2_checked, root7Node136Step1Chunk5_3_checked, root7Node136Step1Chunk5_4_checked, root7Node136Step1Chunk5_5_checked, root7Node136Step1Chunk6_0_checked, root7Node136Step1Chunk6_1_checked, root7Node136Step1Chunk6_2_checked, root7Node136Step1Chunk6_3_checked, root7Node136Step1Chunk6_4_checked, root7Node136Step1Chunk6_5_checked, root7Node136Step1Chunk7_0_checked, root7Node136Step1Chunk7_1_checked, root7Node136Step1Chunk7_2_checked, root7Node136Step1Chunk7_3_checked, root7Node136Step1Chunk7_4_checked, root7Node136Step1Chunk7_5_checked, root7Node136Step1Chunk8_0_checked, root7Node136Step1Chunk8_1_checked, root7Node136Step1Chunk8_2_checked, root7Node136Step1Chunk8_3_checked, root7Node136Step1Chunk8_4_checked, root7Node136Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node136Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,1),(1,4),(6,4)]
  | 4 => [(0,5),(1,2),(6,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3),(1,0),(6,0)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2),(8,2)]
  | 16 => [(5,0),(5,3),(8,0)]
  | 17 => [(4,5),(7,3),(8,5)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(3,4),(5,4)]
  | 24 => [(0,0),(6,3),(6,4)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(4,5),(5,2),(5,5),(8,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(2,3),(4,3)]
  | 32 => [(0,2),(1,5),(3,5),(7,5)]
  | 33 => [(0,3),(1,1),(6,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(4,4),(5,4),(7,2),(8,4)]
  | 36 => [(1,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(6,4),(7,4)]
  | 40 => [(0,5),(1,2),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 42 => [(1,3),(3,3),(5,3),(7,3)]
  | 43 => [(4,1),(7,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(0,3),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(6,5)]
  | 50 => [(5,2),(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(4,2),(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(5,3),(7,0)]
  | 55 => [(2,3),(2,5),(4,5),(8,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(1,4),(6,4)]
  | 58 => [(0,5),(1,2)]
  | 59 => [(4,4),(7,4),(8,4)]
  | _ => [(0,0),(1,3),(6,3),(6,4)]
def root7Node136Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,1),(1,4),(6,4)]
  | 4 => some [(0,5),(1,2),(6,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3),(1,0),(6,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3),(8,0)]
  | 17 => some [(4,5),(7,3),(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(3,4),(5,4)]
  | 24 => some [(0,0),(6,3),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(8,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3),(4,3)]
  | 32 => some [(0,2),(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(1,1),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(5,4),(7,2),(8,4)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(6,4),(7,4)]
  | 40 => some [(0,5),(1,2),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(0,3),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(5,2),(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5),(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(6,3),(6,4)]
theorem root7Node136Domains2_fast_eq : root7Node136Domains2 = expandDomains root7Node136Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node136Domains2 v = expandDomains root7Node136Domains2Fast v from by decide) v
theorem root7Node136Step2Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root7Node136Domains1 root7Node136Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains1 root7Node136Domains2
    root7Node136Domains1Fast root7Node136Domains2Fast
    root7Node136Domains1_fast_eq root7Node136Domains2_fast_eq (by decide)
theorem root7Node136Step2_checked :
    checkReplacement table37 root7Node136Domains1 root7Node136Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node136Step2Chunk0_0_checked, root7Node136Step2Chunk0_1_checked, root7Node136Step2Chunk0_2_checked, root7Node136Step2Chunk0_3_checked, root7Node136Step2Chunk0_4_checked, root7Node136Step2Chunk0_5_checked, root7Node136Step2Chunk1_0_checked, root7Node136Step2Chunk1_1_checked, root7Node136Step2Chunk1_2_checked, root7Node136Step2Chunk1_3_checked, root7Node136Step2Chunk1_4_checked, root7Node136Step2Chunk1_5_checked, root7Node136Step2Chunk2_0_checked, root7Node136Step2Chunk2_1_checked, root7Node136Step2Chunk2_2_checked, root7Node136Step2Chunk2_3_checked, root7Node136Step2Chunk2_4_checked, root7Node136Step2Chunk2_5_checked, root7Node136Step2Chunk3_0_checked, root7Node136Step2Chunk3_1_checked, root7Node136Step2Chunk3_2_checked, root7Node136Step2Chunk3_3_checked, root7Node136Step2Chunk3_4_checked, root7Node136Step2Chunk3_5_checked, root7Node136Step2Chunk4_0_checked, root7Node136Step2Chunk4_1_checked, root7Node136Step2Chunk4_2_checked, root7Node136Step2Chunk4_3_checked, root7Node136Step2Chunk4_4_checked, root7Node136Step2Chunk4_5_checked, root7Node136Step2Chunk5_0_checked, root7Node136Step2Chunk5_1_checked, root7Node136Step2Chunk5_2_checked, root7Node136Step2Chunk5_3_checked, root7Node136Step2Chunk5_4_checked, root7Node136Step2Chunk5_5_checked, root7Node136Step2Chunk6_0_checked, root7Node136Step2Chunk6_1_checked, root7Node136Step2Chunk6_2_checked, root7Node136Step2Chunk6_3_checked, root7Node136Step2Chunk6_4_checked, root7Node136Step2Chunk6_5_checked, root7Node136Step2Chunk7_0_checked, root7Node136Step2Chunk7_1_checked, root7Node136Step2Chunk7_2_checked, root7Node136Step2Chunk7_3_checked, root7Node136Step2Chunk7_4_checked, root7Node136Step2Chunk7_5_checked, root7Node136Step2Chunk8_0_checked, root7Node136Step2Chunk8_1_checked, root7Node136Step2Chunk8_2_checked, root7Node136Step2Chunk8_3_checked, root7Node136Step2Chunk8_4_checked, root7Node136Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node136Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(1,4),(6,4)]
  | 4 => [(0,5),(1,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3),(6,0)]
  | 10 => [(7,1),(8,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2),(8,2)]
  | 16 => [(5,0),(5,3),(8,0)]
  | 17 => [(4,5),(7,3),(8,5)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(3,4),(5,4)]
  | 24 => [(0,0),(6,3),(6,4)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(4,5),(5,2),(5,5),(8,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(2,3),(4,3)]
  | 32 => [(0,2),(1,5),(3,5),(7,5)]
  | 33 => [(0,3),(1,1),(6,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(4,4),(5,4),(7,2),(8,4)]
  | 36 => [(1,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(6,4),(7,4)]
  | 40 => [(0,5),(1,2),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 42 => [(1,3),(3,3),(5,3),(7,3)]
  | 43 => [(4,1),(7,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(0,3),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(6,5)]
  | 50 => [(5,2),(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(4,2),(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(5,3),(7,0)]
  | 55 => [(2,3),(2,5),(4,5),(8,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(1,4),(6,4)]
  | 58 => [(0,5),(1,2)]
  | 59 => [(4,4),(7,4),(8,4)]
  | _ => [(0,0),(1,3),(6,3),(6,4)]
def root7Node136Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4),(6,4)]
  | 4 => some [(0,5),(1,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3),(6,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3),(8,0)]
  | 17 => some [(4,5),(7,3),(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(3,4),(5,4)]
  | 24 => some [(0,0),(6,3),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(8,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3),(4,3)]
  | 32 => some [(0,2),(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(1,1),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(5,4),(7,2),(8,4)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(6,4),(7,4)]
  | 40 => some [(0,5),(1,2),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(0,3),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(5,2),(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5),(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(6,3),(6,4)]
theorem root7Node136Domains3_fast_eq : root7Node136Domains3 = expandDomains root7Node136Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node136Domains3 v = expandDomains root7Node136Domains3Fast v from by decide) v
theorem root7Node136Step3Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root7Node136Domains2 root7Node136Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node136Domains2 root7Node136Domains3
    root7Node136Domains2Fast root7Node136Domains3Fast
    root7Node136Domains2_fast_eq root7Node136Domains3_fast_eq (by decide)
theorem root7Node136Step3_checked :
    checkReplacement table1 root7Node136Domains2 root7Node136Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node136Step3Chunk0_0_checked, root7Node136Step3Chunk0_1_checked, root7Node136Step3Chunk0_2_checked, root7Node136Step3Chunk0_3_checked, root7Node136Step3Chunk0_4_checked, root7Node136Step3Chunk0_5_checked, root7Node136Step3Chunk1_0_checked, root7Node136Step3Chunk1_1_checked, root7Node136Step3Chunk1_2_checked, root7Node136Step3Chunk1_3_checked, root7Node136Step3Chunk1_4_checked, root7Node136Step3Chunk1_5_checked, root7Node136Step3Chunk2_0_checked, root7Node136Step3Chunk2_1_checked, root7Node136Step3Chunk2_2_checked, root7Node136Step3Chunk2_3_checked, root7Node136Step3Chunk2_4_checked, root7Node136Step3Chunk2_5_checked, root7Node136Step3Chunk3_0_checked, root7Node136Step3Chunk3_1_checked, root7Node136Step3Chunk3_2_checked, root7Node136Step3Chunk3_3_checked, root7Node136Step3Chunk3_4_checked, root7Node136Step3Chunk3_5_checked, root7Node136Step3Chunk4_0_checked, root7Node136Step3Chunk4_1_checked, root7Node136Step3Chunk4_2_checked, root7Node136Step3Chunk4_3_checked, root7Node136Step3Chunk4_4_checked, root7Node136Step3Chunk4_5_checked, root7Node136Step3Chunk5_0_checked, root7Node136Step3Chunk5_1_checked, root7Node136Step3Chunk5_2_checked, root7Node136Step3Chunk5_3_checked, root7Node136Step3Chunk5_4_checked, root7Node136Step3Chunk5_5_checked, root7Node136Step3Chunk6_0_checked, root7Node136Step3Chunk6_1_checked, root7Node136Step3Chunk6_2_checked, root7Node136Step3Chunk6_3_checked, root7Node136Step3Chunk6_4_checked, root7Node136Step3Chunk6_5_checked, root7Node136Step3Chunk7_0_checked, root7Node136Step3Chunk7_1_checked, root7Node136Step3Chunk7_2_checked, root7Node136Step3Chunk7_3_checked, root7Node136Step3Chunk7_4_checked, root7Node136Step3Chunk7_5_checked, root7Node136Step3Chunk8_0_checked, root7Node136Step3Chunk8_1_checked, root7Node136Step3Chunk8_2_checked, root7Node136Step3Chunk8_3_checked, root7Node136Step3Chunk8_4_checked, root7Node136Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
