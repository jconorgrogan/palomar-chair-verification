module

public import SpectreFinite.RadiusFiveRoot7Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable0
public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node1Domains0 : Domains 91 State := restrict root7Node0Domains4 25 (0,0)
def root7Node1Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => some [(0,0),(1,3),(1,4),(4,0),(6,4),(7,4),(8,0)]
  | 2 => some [(0,5),(1,2),(1,3),(3,2),(5,2),(6,3),(7,2),(7,3),(8,2)]
  | 3 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(8,0)]
  | 4 => some [(0,0),(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 5 => some [(3,2),(4,2),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 6 => some [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => some [(1,5),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 8 => some [(0,1),(0,2),(0,3),(0,4),(6,0),(6,1),(6,4),(6,5)]
  | 9 => some [(0,4),(1,1),(1,2),(3,1),(5,1),(5,4),(6,2),(7,1)]
  | 10 => some [(0,1),(1,4),(1,5),(6,4),(6,5),(7,4)]
  | 11 => some [(0,4),(0,5),(1,2),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(7,4),(8,4)]
  | 13 => some [(4,0),(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => some [(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 15 => some [(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 16 => some [(0,3),(1,0),(3,0),(4,3),(5,0),(5,3),(8,3)]
  | 17 => some [(2,1),(2,5),(4,1),(4,5),(7,5),(8,5)]
  | 18 => some [(0,2),(0,3),(1,0),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(7,1),(8,1),(8,3)]
  | 20 => some [(1,5),(4,1),(5,1),(6,5),(7,5),(8,1),(8,5)]
  | 21 => some [(4,4),(5,1),(5,4),(7,4),(8,4)]
  | 22 => some [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 23 => some [(0,5),(1,2),(6,2),(7,2)]
  | 24 => some [(2,4),(4,4),(7,4),(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2),(4,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 28 => some [(1,3),(4,5),(7,3),(8,3),(8,5)]
  | 29 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 30 => some [(4,1),(4,3),(5,3),(7,1),(8,1),(8,3)]
  | 31 => some [(0,2),(1,5),(7,5),(8,5)]
  | 32 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 33 => some [(7,1),(8,1)]
  | 34 => some [(1,5),(6,5)]
  | 35 => some [(0,4),(6,1)]
  | 36 => some [(3,4),(5,1),(5,4),(8,1)]
  | 37 => some [(0,0),(0,1),(1,4),(6,3),(6,4),(6,5)]
  | 38 => some [(0,4),(0,5),(1,2),(6,2),(7,2)]
  | 39 => some [(1,4),(3,4),(4,4),(5,4),(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(7,4),(8,0)]
  | 41 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(7,0),(8,0),(8,2)]
  | 43 => some [(5,0),(5,3),(8,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(2,3),(4,3),(8,3)]
  | 47 => some [(0,2),(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 48 => some [(0,3),(1,0),(1,1),(3,0),(6,0),(6,1),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(6,5),(7,5)]
  | 51 => some [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(6,4),(7,4)]
  | 57 => some [(0,5),(1,2),(1,3),(6,3)]
  | 58 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,3),(1,4),(3,3),(4,0),(5,0),(5,3),(6,4),(7,3),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(5,2),(5,5),(6,3),(7,2),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(0,3),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 68 => some [(0,1),(1,4),(1,5),(3,4),(4,1),(5,1),(5,4),(6,5),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4),(7,3)]
  | 71 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => some [(2,0),(4,0),(7,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 75 => some [(3,0),(5,0),(5,3),(7,0),(8,0)]
  | 76 => some [(2,3),(2,5),(4,3),(4,5),(7,3),(8,3),(8,5)]
  | 77 => some [(0,2),(1,0),(1,5),(3,5),(4,2),(5,2),(5,5),(6,0),(7,0),(7,5),(8,2)]
  | 78 => some [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4),(7,4)]
  | 81 => some [(0,5),(1,2),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(3,5),(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(0,3),(1,0),(6,0)]
  | 88 => some [(1,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
theorem root7Node1Domains0_fast_eq : root7Node1Domains0 = expandDomains root7Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node1Domains0 v = expandDomains root7Node1Domains0Fast v from by decide) v
def root7Node1Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => [(1,4),(4,0),(7,4)]
  | 2 => [(0,5),(1,3),(6,3),(7,3)]
  | 3 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 4 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 5 => [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => [(4,1),(5,1),(7,5),(8,1)]
  | 8 => [(0,1),(0,2),(6,0),(6,5)]
  | 9 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 10 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 11 => [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => [(4,0),(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => [(7,3),(8,3)]
  | 15 => [(5,2),(5,5),(8,2)]
  | 16 => [(1,0),(3,0),(5,0)]
  | 17 => [(2,1),(2,5),(4,5)]
  | 18 => [(0,2),(1,0),(6,0),(7,0)]
  | 19 => [(1,1),(4,3),(7,1),(8,3)]
  | 20 => [(4,1),(7,5),(8,5)]
  | 21 => [(4,4),(5,1),(5,4),(7,4),(8,4)]
  | 22 => [(0,1),(1,4),(6,4)]
  | 23 => [(0,5),(1,2),(6,2)]
  | 24 => [(4,4),(8,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2),(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(4,2),(5,2),(8,2)]
  | 30 => [(4,1),(4,3),(5,3),(7,1),(8,1),(8,3)]
  | 31 => [(7,5),(8,5)]
  | 32 => [(0,3),(1,0),(6,0)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1),(8,1)]
  | 37 => [(0,1),(6,5)]
  | 38 => [(0,4),(6,2)]
  | 39 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(7,4),(8,0)]
  | 41 => [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => [(4,2),(8,2)]
  | 43 => [(5,0),(5,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5),(8,5)]
  | 48 => [(1,0),(3,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(6,5),(7,5)]
  | 51 => [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(4,4),(7,2),(8,2)]
  | 59 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => [(0,5),(1,2),(1,3),(3,2),(4,5),(5,2),(5,5),(6,3),(7,2),(7,3),(8,5)]
  | 61 => [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(7,1)]
  | 68 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5)]
  | 70 => [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4),(7,3)]
  | 71 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => [(2,0),(4,0),(7,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2),(8,5)]
  | 75 => [(5,0),(7,0),(8,0)]
  | 76 => [(4,3),(4,5),(7,3),(8,3)]
  | 77 => [(0,2),(1,0),(1,5),(3,5),(4,2),(5,2),(5,5),(6,0),(7,0),(7,5),(8,2)]
  | 78 => [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => [(0,1),(1,4),(6,4),(7,4)]
  | 81 => [(0,5),(1,2),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(7,4),(8,4)]
  | 83 => [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => [(3,5),(4,1),(4,5),(7,5),(8,5)]
  | 87 => [(0,2),(0,3),(1,0),(6,0)]
  | 88 => [(1,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
def root7Node1Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => some [(1,4),(4,0),(7,4)]
  | 2 => some [(0,5),(1,3),(6,3),(7,3)]
  | 3 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 4 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 5 => some [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => some [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => some [(4,1),(5,1),(7,5),(8,1)]
  | 8 => some [(0,1),(0,2),(6,0),(6,5)]
  | 9 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 10 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 11 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(4,0),(5,0),(5,3),(7,0),(8,0),(8,3)]
  | 14 => some [(7,3),(8,3)]
  | 15 => some [(5,2),(5,5),(8,2)]
  | 16 => some [(1,0),(3,0),(5,0)]
  | 17 => some [(2,1),(2,5),(4,5)]
  | 18 => some [(0,2),(1,0),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(4,4),(5,1),(5,4),(7,4),(8,4)]
  | 22 => some [(0,1),(1,4),(6,4)]
  | 23 => some [(0,5),(1,2),(6,2)]
  | 24 => some [(4,4),(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(4,2),(5,2),(8,2)]
  | 30 => some [(4,1),(4,3),(5,3),(7,1),(8,1),(8,3)]
  | 31 => some [(7,5),(8,5)]
  | 32 => some [(0,3),(1,0),(6,0)]
  | 33 => some [(7,1),(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1),(8,1)]
  | 37 => some [(0,1),(6,5)]
  | 38 => some [(0,4),(6,2)]
  | 39 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => some [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(7,4),(8,0)]
  | 41 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 42 => some [(4,2),(8,2)]
  | 43 => some [(5,0),(5,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5),(8,5)]
  | 48 => some [(1,0),(3,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(6,5),(7,5)]
  | 51 => some [(0,0),(0,1),(0,4),(0,5),(6,2),(6,3),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 53 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(5,2),(5,5),(6,3),(7,2),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0),(1,1),(3,0),(4,3),(6,1),(7,0),(7,1)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(7,5),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4),(7,3)]
  | 71 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 72 => some [(2,0),(4,0),(7,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2),(8,5)]
  | 75 => some [(5,0),(7,0),(8,0)]
  | 76 => some [(4,3),(4,5),(7,3),(8,3)]
  | 77 => some [(0,2),(1,0),(1,5),(3,5),(4,2),(5,2),(5,5),(6,0),(7,0),(7,5),(8,2)]
  | 78 => some [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => some [(0,1),(1,4),(6,4),(7,4)]
  | 81 => some [(0,5),(1,2),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(7,4),(8,4)]
  | 83 => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(3,5),(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(0,3),(1,0),(6,0)]
  | 88 => some [(1,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
theorem root7Node1Domains1_fast_eq : root7Node1Domains1 = expandDomains root7Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node1Domains1 v = expandDomains root7Node1Domains1Fast v from by decide) v
theorem root7Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq (by decide)
theorem root7Node1Step1Narrowing_checked :
    checkNarrowing table35 root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkNarrowing_flatten table35Scope [table35Rows0_0,table35Rows0_1,table35Rows0_2,table35Rows0_3,table35Rows0_4,table35Rows0_5,table35Rows1_0,table35Rows1_1,table35Rows1_2,table35Rows1_3,table35Rows1_4,table35Rows1_5,table35Rows2_0,table35Rows2_1,table35Rows2_2,table35Rows2_3,table35Rows2_4,table35Rows2_5,table35Rows3_0,table35Rows3_1,table35Rows3_2,table35Rows3_3,table35Rows3_4,table35Rows3_5,table35Rows4_0,table35Rows4_1,table35Rows4_2,table35Rows4_3,table35Rows4_4,table35Rows4_5,table35Rows5_0,table35Rows5_1,table35Rows5_2,table35Rows5_3,table35Rows5_4,table35Rows5_5,table35Rows6_0,table35Rows6_1,table35Rows6_2,table35Rows6_3,table35Rows6_4,table35Rows6_5,table35Rows7_0,table35Rows7_1,table35Rows7_2,table35Rows7_3,table35Rows7_4,table35Rows7_5,table35Rows8_0,table35Rows8_1,table35Rows8_2,table35Rows8_3,table35Rows8_4,table35Rows8_5]
    root7Node1Domains0 root7Node1Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node1Step1Chunk0_0_checked, root7Node1Step1Chunk0_1_checked, root7Node1Step1Chunk0_2_checked, root7Node1Step1Chunk0_3_checked, root7Node1Step1Chunk0_4_checked, root7Node1Step1Chunk0_5_checked, root7Node1Step1Chunk1_0_checked, root7Node1Step1Chunk1_1_checked, root7Node1Step1Chunk1_2_checked, root7Node1Step1Chunk1_3_checked, root7Node1Step1Chunk1_4_checked, root7Node1Step1Chunk1_5_checked, root7Node1Step1Chunk2_0_checked, root7Node1Step1Chunk2_1_checked, root7Node1Step1Chunk2_2_checked, root7Node1Step1Chunk2_3_checked, root7Node1Step1Chunk2_4_checked, root7Node1Step1Chunk2_5_checked, root7Node1Step1Chunk3_0_checked, root7Node1Step1Chunk3_1_checked, root7Node1Step1Chunk3_2_checked, root7Node1Step1Chunk3_3_checked, root7Node1Step1Chunk3_4_checked, root7Node1Step1Chunk3_5_checked, root7Node1Step1Chunk4_0_checked, root7Node1Step1Chunk4_1_checked, root7Node1Step1Chunk4_2_checked, root7Node1Step1Chunk4_3_checked, root7Node1Step1Chunk4_4_checked, root7Node1Step1Chunk4_5_checked, root7Node1Step1Chunk5_0_checked, root7Node1Step1Chunk5_1_checked, root7Node1Step1Chunk5_2_checked, root7Node1Step1Chunk5_3_checked, root7Node1Step1Chunk5_4_checked, root7Node1Step1Chunk5_5_checked, root7Node1Step1Chunk6_0_checked, root7Node1Step1Chunk6_1_checked, root7Node1Step1Chunk6_2_checked, root7Node1Step1Chunk6_3_checked, root7Node1Step1Chunk6_4_checked, root7Node1Step1Chunk6_5_checked, root7Node1Step1Chunk7_0_checked, root7Node1Step1Chunk7_1_checked, root7Node1Step1Chunk7_2_checked, root7Node1Step1Chunk7_3_checked, root7Node1Step1Chunk7_4_checked, root7Node1Step1Chunk7_5_checked, root7Node1Step1Chunk8_0_checked, root7Node1Step1Chunk8_1_checked, root7Node1Step1Chunk8_2_checked, root7Node1Step1Chunk8_3_checked, root7Node1Step1Chunk8_4_checked, root7Node1Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node1Step1_checked :
    checkReplacement table35 root7Node1Domains0 root7Node1Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node1Domains0 root7Node1Domains1
    root7Node1Domains0Fast root7Node1Domains1Fast
    root7Node1Domains0_fast_eq root7Node1Domains1_fast_eq
    root7Node1Step1Narrowing_checked (by decide)
def root7Node1Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => [(1,4),(4,0),(7,4)]
  | 2 => [(0,5),(1,3),(6,3),(7,3)]
  | 3 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 4 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 5 => [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => [(4,1),(5,1),(7,5),(8,1)]
  | 8 => [(0,1),(0,2),(6,0),(6,5)]
  | 9 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 10 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 11 => [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => [(4,0),(7,0),(8,0)]
  | 14 => [(7,3),(8,3)]
  | 15 => [(5,2),(5,5),(8,2)]
  | 16 => [(1,0),(3,0),(5,0)]
  | 17 => [(2,1),(2,5),(4,5)]
  | 18 => [(0,2),(1,0),(6,0),(7,0)]
  | 19 => [(1,1),(4,3),(7,1),(8,3)]
  | 20 => [(4,1),(7,5),(8,5)]
  | 21 => [(4,4),(5,1),(5,4),(8,4)]
  | 22 => [(0,1),(1,4),(6,4)]
  | 23 => [(0,5),(1,2),(6,2)]
  | 24 => [(4,4),(8,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2),(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(4,2),(5,2),(8,2)]
  | 30 => [(4,3),(5,3),(7,1),(8,3)]
  | 31 => [(7,5),(8,5)]
  | 32 => [(0,3),(1,0),(6,0)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1),(8,1)]
  | 37 => [(0,1),(6,5)]
  | 38 => [(0,4),(6,2)]
  | 39 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => [(4,0),(7,4),(8,0)]
  | 41 => [(1,3),(7,3)]
  | 42 => [(4,2),(8,2)]
  | 43 => [(5,0),(5,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5),(8,5)]
  | 48 => [(1,0),(3,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(6,5),(7,5)]
  | 51 => [(0,1),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(6,2)]
  | 53 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(4,4),(7,2),(8,2)]
  | 59 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => [(0,5),(1,2),(1,3),(3,2),(4,5),(5,2),(5,5),(6,3),(7,2),(7,3),(8,5)]
  | 61 => [(0,3),(1,0),(3,0),(7,0)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(7,1)]
  | 68 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5)]
  | 70 => [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4)]
  | 71 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 72 => [(2,0),(4,0),(7,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2),(8,5)]
  | 75 => [(5,0),(7,0),(8,0)]
  | 76 => [(4,3),(4,5),(7,3),(8,3)]
  | 77 => [(0,2),(1,0),(1,5),(3,5),(4,2),(5,2),(5,5),(6,0),(7,0),(7,5),(8,2)]
  | 78 => [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => [(0,1),(1,4),(7,4)]
  | 81 => [(0,5),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(8,4)]
  | 83 => [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => [(4,1),(4,5),(7,5),(8,5)]
  | 87 => [(0,2),(1,0),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
def root7Node1Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => some [(1,4),(4,0),(7,4)]
  | 2 => some [(0,5),(1,3),(6,3),(7,3)]
  | 3 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 4 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 5 => some [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => some [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => some [(4,1),(5,1),(7,5),(8,1)]
  | 8 => some [(0,1),(0,2),(6,0),(6,5)]
  | 9 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 10 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 11 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(4,0),(7,0),(8,0)]
  | 14 => some [(7,3),(8,3)]
  | 15 => some [(5,2),(5,5),(8,2)]
  | 16 => some [(1,0),(3,0),(5,0)]
  | 17 => some [(2,1),(2,5),(4,5)]
  | 18 => some [(0,2),(1,0),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(4,4),(5,1),(5,4),(8,4)]
  | 22 => some [(0,1),(1,4),(6,4)]
  | 23 => some [(0,5),(1,2),(6,2)]
  | 24 => some [(4,4),(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(4,2),(5,2),(8,2)]
  | 30 => some [(4,3),(5,3),(7,1),(8,3)]
  | 31 => some [(7,5),(8,5)]
  | 32 => some [(0,3),(1,0),(6,0)]
  | 33 => some [(7,1),(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1),(8,1)]
  | 37 => some [(0,1),(6,5)]
  | 38 => some [(0,4),(6,2)]
  | 39 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => some [(4,0),(7,4),(8,0)]
  | 41 => some [(1,3),(7,3)]
  | 42 => some [(4,2),(8,2)]
  | 43 => some [(5,0),(5,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5),(8,5)]
  | 48 => some [(1,0),(3,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(6,5),(7,5)]
  | 51 => some [(0,1),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(6,2)]
  | 53 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(5,2),(5,5),(6,3),(7,2),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4)]
  | 71 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 72 => some [(2,0),(4,0),(7,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2),(8,5)]
  | 75 => some [(5,0),(7,0),(8,0)]
  | 76 => some [(4,3),(4,5),(7,3),(8,3)]
  | 77 => some [(0,2),(1,0),(1,5),(3,5),(4,2),(5,2),(5,5),(6,0),(7,0),(7,5),(8,2)]
  | 78 => some [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => some [(0,1),(1,4),(7,4)]
  | 81 => some [(0,5),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(8,4)]
  | 83 => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2),(8,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(1,0),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(0,2),(1,5),(4,1),(6,5),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(0,4),(1,1),(6,0),(6,1),(6,5)]
theorem root7Node1Domains2_fast_eq : root7Node1Domains2 = expandDomains root7Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node1Domains2 v = expandDomains root7Node1Domains2Fast v from by decide) v
theorem root7Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq (by decide)
theorem root7Node1Step2Narrowing_checked :
    checkNarrowing table54 root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root7Node1Domains1 root7Node1Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node1Step2Chunk0_0_checked, root7Node1Step2Chunk0_1_checked, root7Node1Step2Chunk0_2_checked, root7Node1Step2Chunk0_3_checked, root7Node1Step2Chunk0_4_checked, root7Node1Step2Chunk0_5_checked, root7Node1Step2Chunk1_0_checked, root7Node1Step2Chunk1_1_checked, root7Node1Step2Chunk1_2_checked, root7Node1Step2Chunk1_3_checked, root7Node1Step2Chunk1_4_checked, root7Node1Step2Chunk1_5_checked, root7Node1Step2Chunk2_0_checked, root7Node1Step2Chunk2_1_checked, root7Node1Step2Chunk2_2_checked, root7Node1Step2Chunk2_3_checked, root7Node1Step2Chunk2_4_checked, root7Node1Step2Chunk2_5_checked, root7Node1Step2Chunk3_0_checked, root7Node1Step2Chunk3_1_checked, root7Node1Step2Chunk3_2_checked, root7Node1Step2Chunk3_3_checked, root7Node1Step2Chunk3_4_checked, root7Node1Step2Chunk3_5_checked, root7Node1Step2Chunk4_0_checked, root7Node1Step2Chunk4_1_checked, root7Node1Step2Chunk4_2_checked, root7Node1Step2Chunk4_3_checked, root7Node1Step2Chunk4_4_checked, root7Node1Step2Chunk4_5_checked, root7Node1Step2Chunk5_0_checked, root7Node1Step2Chunk5_1_checked, root7Node1Step2Chunk5_2_checked, root7Node1Step2Chunk5_3_checked, root7Node1Step2Chunk5_4_checked, root7Node1Step2Chunk5_5_checked, root7Node1Step2Chunk6_0_checked, root7Node1Step2Chunk6_1_checked, root7Node1Step2Chunk6_2_checked, root7Node1Step2Chunk6_3_checked, root7Node1Step2Chunk6_4_checked, root7Node1Step2Chunk6_5_checked, root7Node1Step2Chunk7_0_checked, root7Node1Step2Chunk7_1_checked, root7Node1Step2Chunk7_2_checked, root7Node1Step2Chunk7_3_checked, root7Node1Step2Chunk7_4_checked, root7Node1Step2Chunk7_5_checked, root7Node1Step2Chunk8_0_checked, root7Node1Step2Chunk8_1_checked, root7Node1Step2Chunk8_2_checked, root7Node1Step2Chunk8_3_checked, root7Node1Step2Chunk8_4_checked, root7Node1Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node1Step2_checked :
    checkReplacement table54 root7Node1Domains1 root7Node1Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node1Domains1 root7Node1Domains2
    root7Node1Domains1Fast root7Node1Domains2Fast
    root7Node1Domains1_fast_eq root7Node1Domains2_fast_eq
    root7Node1Step2Narrowing_checked (by decide)
def root7Node1Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => [(1,4),(4,0),(7,4)]
  | 2 => [(0,5),(1,3),(6,3),(7,3)]
  | 3 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 4 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 5 => [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => [(4,1),(5,1),(7,5),(8,1)]
  | 8 => [(0,1),(0,2),(6,0),(6,5)]
  | 9 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 10 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 11 => [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => [(4,0),(7,0),(8,0)]
  | 14 => [(7,3),(8,3)]
  | 15 => [(5,2),(5,5),(8,2)]
  | 16 => [(1,0),(3,0),(5,0)]
  | 17 => [(2,1),(2,5),(4,5)]
  | 18 => [(0,2),(1,0),(6,0),(7,0)]
  | 19 => [(1,1),(4,3),(7,1),(8,3)]
  | 20 => [(4,1),(7,5),(8,5)]
  | 21 => [(4,4),(5,1),(5,4),(8,4)]
  | 22 => [(0,1),(1,4),(6,4)]
  | 23 => [(0,5),(1,2),(6,2)]
  | 24 => [(4,4),(8,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2),(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(4,2),(5,2),(8,2)]
  | 30 => [(4,3),(5,3),(7,1),(8,3)]
  | 31 => [(7,5),(8,5)]
  | 32 => [(0,3),(1,0),(6,0)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1),(8,1)]
  | 37 => [(0,1),(6,5)]
  | 38 => [(0,4),(6,2)]
  | 39 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => [(4,0),(7,4),(8,0)]
  | 41 => [(1,3),(7,3)]
  | 42 => [(4,2),(8,2)]
  | 43 => [(5,0),(5,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5),(8,5)]
  | 48 => [(1,0),(3,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => [(0,1),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(6,2)]
  | 53 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(4,4),(7,2),(8,2)]
  | 59 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => [(0,3),(1,0),(3,0),(7,0)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(7,1)]
  | 68 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4)]
  | 71 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 72 => [(2,0),(4,0),(7,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2),(8,5)]
  | 75 => [(5,0),(7,0),(8,0)]
  | 76 => [(4,3),(4,5),(7,3),(8,3)]
  | 77 => [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(7,5),(8,2)]
  | 78 => [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => [(0,1),(1,4),(7,4)]
  | 81 => [(0,5),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(8,4)]
  | 83 => [(0,0),(1,4),(6,4),(7,4)]
  | 84 => [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => [(4,1),(4,5),(7,5),(8,5)]
  | 87 => [(0,2),(1,0),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(1,5),(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,1),(6,5)]
def root7Node1Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(2,4),(4,4),(7,2),(7,4),(8,2),(8,4)]
  | 1 => some [(1,4),(4,0),(7,4)]
  | 2 => some [(0,5),(1,3),(6,3),(7,3)]
  | 3 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 4 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 5 => some [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => some [(0,4),(1,1),(6,1),(7,1),(8,1)]
  | 7 => some [(4,1),(5,1),(7,5),(8,1)]
  | 8 => some [(0,1),(0,2),(6,0),(6,5)]
  | 9 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 10 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 11 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(4,0),(7,0),(8,0)]
  | 14 => some [(7,3),(8,3)]
  | 15 => some [(5,2),(5,5),(8,2)]
  | 16 => some [(1,0),(3,0),(5,0)]
  | 17 => some [(2,1),(2,5),(4,5)]
  | 18 => some [(0,2),(1,0),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(4,4),(5,1),(5,4),(8,4)]
  | 22 => some [(0,1),(1,4),(6,4)]
  | 23 => some [(0,5),(1,2),(6,2)]
  | 24 => some [(4,4),(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(4,2),(5,2),(8,2)]
  | 30 => some [(4,3),(5,3),(7,1),(8,3)]
  | 31 => some [(7,5),(8,5)]
  | 32 => some [(0,3),(1,0),(6,0)]
  | 33 => some [(7,1),(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1),(8,1)]
  | 37 => some [(0,1),(6,5)]
  | 38 => some [(0,4),(6,2)]
  | 39 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => some [(4,0),(7,4),(8,0)]
  | 41 => some [(1,3),(7,3)]
  | 42 => some [(4,2),(8,2)]
  | 43 => some [(5,0),(5,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5),(8,5)]
  | 48 => some [(1,0),(3,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => some [(0,1),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(6,2)]
  | 53 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => some [(0,3),(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4)]
  | 71 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 72 => some [(2,0),(4,0),(7,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2),(8,5)]
  | 75 => some [(5,0),(7,0),(8,0)]
  | 76 => some [(4,3),(4,5),(7,3),(8,3)]
  | 77 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(7,5),(8,2)]
  | 78 => some [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => some [(0,1),(1,4),(7,4)]
  | 81 => some [(0,5),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(8,4)]
  | 83 => some [(0,0),(1,4),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(1,0),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(1,5),(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(6,0),(6,1),(6,5)]
theorem root7Node1Domains3_fast_eq : root7Node1Domains3 = expandDomains root7Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node1Domains3 v = expandDomains root7Node1Domains3Fast v from by decide) v
theorem root7Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq (by decide)
theorem root7Node1Step3Narrowing_checked :
    checkNarrowing table57 root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root7Node1Domains2 root7Node1Domains3 (by
      simp only [List.all_cons, List.all_nil, root7Node1Step3Chunk0_0_checked, root7Node1Step3Chunk0_1_checked, root7Node1Step3Chunk0_2_checked, root7Node1Step3Chunk0_3_checked, root7Node1Step3Chunk0_4_checked, root7Node1Step3Chunk0_5_checked, root7Node1Step3Chunk1_0_checked, root7Node1Step3Chunk1_1_checked, root7Node1Step3Chunk1_2_checked, root7Node1Step3Chunk1_3_checked, root7Node1Step3Chunk1_4_checked, root7Node1Step3Chunk1_5_checked, root7Node1Step3Chunk2_0_checked, root7Node1Step3Chunk2_1_checked, root7Node1Step3Chunk2_2_checked, root7Node1Step3Chunk2_3_checked, root7Node1Step3Chunk2_4_checked, root7Node1Step3Chunk2_5_checked, root7Node1Step3Chunk3_0_checked, root7Node1Step3Chunk3_1_checked, root7Node1Step3Chunk3_2_checked, root7Node1Step3Chunk3_3_checked, root7Node1Step3Chunk3_4_checked, root7Node1Step3Chunk3_5_checked, root7Node1Step3Chunk4_0_checked, root7Node1Step3Chunk4_1_checked, root7Node1Step3Chunk4_2_checked, root7Node1Step3Chunk4_3_checked, root7Node1Step3Chunk4_4_checked, root7Node1Step3Chunk4_5_checked, root7Node1Step3Chunk5_0_checked, root7Node1Step3Chunk5_1_checked, root7Node1Step3Chunk5_2_checked, root7Node1Step3Chunk5_3_checked, root7Node1Step3Chunk5_4_checked, root7Node1Step3Chunk5_5_checked, root7Node1Step3Chunk6_0_checked, root7Node1Step3Chunk6_1_checked, root7Node1Step3Chunk6_2_checked, root7Node1Step3Chunk6_3_checked, root7Node1Step3Chunk6_4_checked, root7Node1Step3Chunk6_5_checked, root7Node1Step3Chunk7_0_checked, root7Node1Step3Chunk7_1_checked, root7Node1Step3Chunk7_2_checked, root7Node1Step3Chunk7_3_checked, root7Node1Step3Chunk7_4_checked, root7Node1Step3Chunk7_5_checked, root7Node1Step3Chunk8_0_checked, root7Node1Step3Chunk8_1_checked, root7Node1Step3Chunk8_2_checked, root7Node1Step3Chunk8_3_checked, root7Node1Step3Chunk8_4_checked, root7Node1Step3Chunk8_5_checked, Bool.true_and])
theorem root7Node1Step3_checked :
    checkReplacement table57 root7Node1Domains2 root7Node1Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root7Node1Domains2 root7Node1Domains3
    root7Node1Domains2Fast root7Node1Domains3Fast
    root7Node1Domains2_fast_eq root7Node1Domains3_fast_eq
    root7Node1Step3Narrowing_checked (by decide)
def root7Node1Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(7,2),(8,4)]
  | 1 => [(1,4),(4,0),(7,4)]
  | 2 => [(0,5),(1,3),(6,3),(7,3)]
  | 3 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 4 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 5 => [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => [(1,1),(6,1),(7,1)]
  | 7 => [(4,1),(5,1),(7,5),(8,1)]
  | 8 => [(0,1),(0,2),(6,0),(6,5)]
  | 9 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 10 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 11 => [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => [(4,0),(7,0),(8,0)]
  | 14 => [(7,3),(8,3)]
  | 15 => [(5,2),(5,5),(8,2)]
  | 16 => [(1,0),(3,0),(5,0)]
  | 17 => [(2,1),(2,5),(4,5)]
  | 18 => [(0,2),(1,0),(6,0),(7,0)]
  | 19 => [(1,1),(4,3),(7,1),(8,3)]
  | 20 => [(4,1),(7,5),(8,5)]
  | 21 => [(4,4),(5,1),(5,4),(8,4)]
  | 22 => [(0,1),(1,4),(6,4)]
  | 23 => [(0,5),(1,2),(6,2)]
  | 24 => [(4,4),(8,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2),(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(4,2),(5,2),(8,2)]
  | 30 => [(4,3),(5,3),(7,1),(8,3)]
  | 31 => [(7,5),(8,5)]
  | 32 => [(0,3),(1,0),(6,0)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1),(8,1)]
  | 37 => [(0,1),(6,5)]
  | 38 => [(0,4),(6,2)]
  | 39 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => [(4,0),(7,4),(8,0)]
  | 41 => [(1,3),(7,3)]
  | 42 => [(4,2),(8,2)]
  | 43 => [(5,0),(5,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5),(8,5)]
  | 48 => [(1,0),(3,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => [(0,1),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(6,2)]
  | 53 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(4,4),(7,2),(8,2)]
  | 59 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => [(0,3),(1,0),(3,0),(7,0)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(7,1)]
  | 68 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4)]
  | 71 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 72 => [(2,0),(4,0),(7,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2),(8,5)]
  | 75 => [(5,0),(7,0),(8,0)]
  | 76 => [(4,3),(4,5),(7,3),(8,3)]
  | 77 => [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(7,5),(8,2)]
  | 78 => [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => [(0,1),(1,4),(7,4)]
  | 81 => [(0,5),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(8,4)]
  | 83 => [(0,0),(1,4),(6,4),(7,4)]
  | 84 => [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => [(4,1),(4,5),(7,5),(8,5)]
  | 87 => [(0,2),(1,0),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(1,5),(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,1),(6,5)]
def root7Node1Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(7,2),(8,4)]
  | 1 => some [(1,4),(4,0),(7,4)]
  | 2 => some [(0,5),(1,3),(6,3),(7,3)]
  | 3 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 4 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 5 => some [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => some [(1,1),(6,1),(7,1)]
  | 7 => some [(4,1),(5,1),(7,5),(8,1)]
  | 8 => some [(0,1),(0,2),(6,0),(6,5)]
  | 9 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 10 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 11 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(4,0),(7,0),(8,0)]
  | 14 => some [(7,3),(8,3)]
  | 15 => some [(5,2),(5,5),(8,2)]
  | 16 => some [(1,0),(3,0),(5,0)]
  | 17 => some [(2,1),(2,5),(4,5)]
  | 18 => some [(0,2),(1,0),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(4,4),(5,1),(5,4),(8,4)]
  | 22 => some [(0,1),(1,4),(6,4)]
  | 23 => some [(0,5),(1,2),(6,2)]
  | 24 => some [(4,4),(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(4,2),(5,2),(8,2)]
  | 30 => some [(4,3),(5,3),(7,1),(8,3)]
  | 31 => some [(7,5),(8,5)]
  | 32 => some [(0,3),(1,0),(6,0)]
  | 33 => some [(7,1),(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1),(8,1)]
  | 37 => some [(0,1),(6,5)]
  | 38 => some [(0,4),(6,2)]
  | 39 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => some [(4,0),(7,4),(8,0)]
  | 41 => some [(1,3),(7,3)]
  | 42 => some [(4,2),(8,2)]
  | 43 => some [(5,0),(5,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5),(8,5)]
  | 48 => some [(1,0),(3,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => some [(0,1),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(6,2)]
  | 53 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => some [(0,3),(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4)]
  | 71 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 72 => some [(2,0),(4,0),(7,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2),(8,5)]
  | 75 => some [(5,0),(7,0),(8,0)]
  | 76 => some [(4,3),(4,5),(7,3),(8,3)]
  | 77 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(7,5),(8,2)]
  | 78 => some [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => some [(0,1),(1,4),(7,4)]
  | 81 => some [(0,5),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(8,4)]
  | 83 => some [(0,0),(1,4),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(1,0),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(1,5),(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(6,0),(6,1),(6,5)]
theorem root7Node1Domains4_fast_eq : root7Node1Domains4 = expandDomains root7Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node1Domains4 v = expandDomains root7Node1Domains4Fast v from by decide) v
theorem root7Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq (by decide)
theorem root7Node1Step4Narrowing_checked :
    checkNarrowing table0 root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkNarrowing_flatten table0Scope [table0Rows0_0,table0Rows0_1,table0Rows0_2,table0Rows0_3,table0Rows0_4,table0Rows0_5,table0Rows1_0,table0Rows1_1,table0Rows1_2,table0Rows1_3,table0Rows1_4,table0Rows1_5,table0Rows2_0,table0Rows2_1,table0Rows2_2,table0Rows2_3,table0Rows2_4,table0Rows2_5,table0Rows3_0,table0Rows3_1,table0Rows3_2,table0Rows3_3,table0Rows3_4,table0Rows3_5,table0Rows4_0,table0Rows4_1,table0Rows4_2,table0Rows4_3,table0Rows4_4,table0Rows4_5,table0Rows5_0,table0Rows5_1,table0Rows5_2,table0Rows5_3,table0Rows5_4,table0Rows5_5,table0Rows6_0,table0Rows6_1,table0Rows6_2,table0Rows6_3,table0Rows6_4,table0Rows6_5,table0Rows7_0,table0Rows7_1,table0Rows7_2,table0Rows7_3,table0Rows7_4,table0Rows7_5,table0Rows8_0,table0Rows8_1,table0Rows8_2,table0Rows8_3,table0Rows8_4,table0Rows8_5]
    root7Node1Domains3 root7Node1Domains4 (by
      simp only [List.all_cons, List.all_nil, root7Node1Step4Chunk0_0_checked, root7Node1Step4Chunk0_1_checked, root7Node1Step4Chunk0_2_checked, root7Node1Step4Chunk0_3_checked, root7Node1Step4Chunk0_4_checked, root7Node1Step4Chunk0_5_checked, root7Node1Step4Chunk1_0_checked, root7Node1Step4Chunk1_1_checked, root7Node1Step4Chunk1_2_checked, root7Node1Step4Chunk1_3_checked, root7Node1Step4Chunk1_4_checked, root7Node1Step4Chunk1_5_checked, root7Node1Step4Chunk2_0_checked, root7Node1Step4Chunk2_1_checked, root7Node1Step4Chunk2_2_checked, root7Node1Step4Chunk2_3_checked, root7Node1Step4Chunk2_4_checked, root7Node1Step4Chunk2_5_checked, root7Node1Step4Chunk3_0_checked, root7Node1Step4Chunk3_1_checked, root7Node1Step4Chunk3_2_checked, root7Node1Step4Chunk3_3_checked, root7Node1Step4Chunk3_4_checked, root7Node1Step4Chunk3_5_checked, root7Node1Step4Chunk4_0_checked, root7Node1Step4Chunk4_1_checked, root7Node1Step4Chunk4_2_checked, root7Node1Step4Chunk4_3_checked, root7Node1Step4Chunk4_4_checked, root7Node1Step4Chunk4_5_checked, root7Node1Step4Chunk5_0_checked, root7Node1Step4Chunk5_1_checked, root7Node1Step4Chunk5_2_checked, root7Node1Step4Chunk5_3_checked, root7Node1Step4Chunk5_4_checked, root7Node1Step4Chunk5_5_checked, root7Node1Step4Chunk6_0_checked, root7Node1Step4Chunk6_1_checked, root7Node1Step4Chunk6_2_checked, root7Node1Step4Chunk6_3_checked, root7Node1Step4Chunk6_4_checked, root7Node1Step4Chunk6_5_checked, root7Node1Step4Chunk7_0_checked, root7Node1Step4Chunk7_1_checked, root7Node1Step4Chunk7_2_checked, root7Node1Step4Chunk7_3_checked, root7Node1Step4Chunk7_4_checked, root7Node1Step4Chunk7_5_checked, root7Node1Step4Chunk8_0_checked, root7Node1Step4Chunk8_1_checked, root7Node1Step4Chunk8_2_checked, root7Node1Step4Chunk8_3_checked, root7Node1Step4Chunk8_4_checked, root7Node1Step4Chunk8_5_checked, Bool.true_and])
theorem root7Node1Step4_checked :
    checkReplacement table0 root7Node1Domains3 root7Node1Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root7Node1Domains3 root7Node1Domains4
    root7Node1Domains3Fast root7Node1Domains4Fast
    root7Node1Domains3_fast_eq root7Node1Domains4_fast_eq
    root7Node1Step4Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
