module

public import SpectreFinite.LargerWindowIndexedPruning
public import SpectreFinite.RadiusThreeRowProjection
public import SpectreFinite.RadiusFourPruningLiteralDomain
public import SpectreFinite.RadiusFourPruningGeometry

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem indexedLookup0 (row : List State) : patchState (literalDomain.zip row) (-4,0) = (row[0]?).getD (0,0) := patchState_zip_index literalDomain row (-4,0) 0 (by decide) (by decide)
theorem indexedLookup1 (row : List State) : patchState (literalDomain.zip row) (-4,1) = (row[1]?).getD (0,0) := patchState_zip_index literalDomain row (-4,1) 1 (by decide) (by decide)
theorem indexedLookup3 (row : List State) : patchState (literalDomain.zip row) (-4,3) = (row[3]?).getD (0,0) := patchState_zip_index literalDomain row (-4,3) 3 (by decide) (by decide)
theorem indexedLookup4 (row : List State) : patchState (literalDomain.zip row) (-4,4) = (row[4]?).getD (0,0) := patchState_zip_index literalDomain row (-4,4) 4 (by decide) (by decide)
theorem indexedLookup5 (row : List State) : patchState (literalDomain.zip row) (-3,-1) = (row[5]?).getD (0,0) := patchState_zip_index literalDomain row (-3,-1) 5 (by decide) (by decide)
theorem indexedLookup6 (row : List State) : patchState (literalDomain.zip row) (-3,0) = (row[6]?).getD (0,0) := patchState_zip_index literalDomain row (-3,0) 6 (by decide) (by decide)
theorem indexedLookup9 (row : List State) : patchState (literalDomain.zip row) (-3,3) = (row[9]?).getD (0,0) := patchState_zip_index literalDomain row (-3,3) 9 (by decide) (by decide)
theorem indexedLookup10 (row : List State) : patchState (literalDomain.zip row) (-3,4) = (row[10]?).getD (0,0) := patchState_zip_index literalDomain row (-3,4) 10 (by decide) (by decide)
theorem indexedLookup25 (row : List State) : patchState (literalDomain.zip row) (-1,4) = (row[25]?).getD (0,0) := patchState_zip_index literalDomain row (-1,4) 25 (by decide) (by decide)
theorem indexedLookup26 (row : List State) : patchState (literalDomain.zip row) (0,-4) = (row[26]?).getD (0,0) := patchState_zip_index literalDomain row (0,-4) 26 (by decide) (by decide)
theorem indexedLookup27 (row : List State) : patchState (literalDomain.zip row) (0,-3) = (row[27]?).getD (0,0) := patchState_zip_index literalDomain row (0,-3) 27 (by decide) (by decide)
theorem indexedLookup33 (row : List State) : patchState (literalDomain.zip row) (0,3) = (row[33]?).getD (0,0) := patchState_zip_index literalDomain row (0,3) 33 (by decide) (by decide)
theorem indexedLookup34 (row : List State) : patchState (literalDomain.zip row) (0,4) = (row[34]?).getD (0,0) := patchState_zip_index literalDomain row (0,4) 34 (by decide) (by decide)
theorem indexedLookup35 (row : List State) : patchState (literalDomain.zip row) (1,-4) = (row[35]?).getD (0,0) := patchState_zip_index literalDomain row (1,-4) 35 (by decide) (by decide)
theorem indexedLookup42 (row : List State) : patchState (literalDomain.zip row) (1,3) = (row[42]?).getD (0,0) := patchState_zip_index literalDomain row (1,3) 42 (by decide) (by decide)
theorem indexedLookup50 (row : List State) : patchState (literalDomain.zip row) (3,-4) = (row[50]?).getD (0,0) := patchState_zip_index literalDomain row (3,-4) 50 (by decide) (by decide)
theorem indexedLookup51 (row : List State) : patchState (literalDomain.zip row) (3,-3) = (row[51]?).getD (0,0) := patchState_zip_index literalDomain row (3,-3) 51 (by decide) (by decide)
theorem indexedLookup54 (row : List State) : patchState (literalDomain.zip row) (3,0) = (row[54]?).getD (0,0) := patchState_zip_index literalDomain row (3,0) 54 (by decide) (by decide)
theorem indexedLookup55 (row : List State) : patchState (literalDomain.zip row) (3,1) = (row[55]?).getD (0,0) := patchState_zip_index literalDomain row (3,1) 55 (by decide) (by decide)
theorem indexedLookup56 (row : List State) : patchState (literalDomain.zip row) (4,-4) = (row[56]?).getD (0,0) := patchState_zip_index literalDomain row (4,-4) 56 (by decide) (by decide)
theorem indexedLookup57 (row : List State) : patchState (literalDomain.zip row) (4,-3) = (row[57]?).getD (0,0) := patchState_zip_index literalDomain row (4,-3) 57 (by decide) (by decide)
theorem indexedLookup59 (row : List State) : patchState (literalDomain.zip row) (4,-1) = (row[59]?).getD (0,0) := patchState_zip_index literalDomain row (4,-1) 59 (by decide) (by decide)
theorem indexedLookup60 (row : List State) : patchState (literalDomain.zip row) (4,0) = (row[60]?).getD (0,0) := patchState_zip_index literalDomain row (4,0) 60 (by decide) (by decide)
def leftIndices0 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [0, 4, 26, 50, 51, 54]
  | 1 => [5, 26, 54, 56, 59]
  | 2 => [33, 35, 42, 56, 60]
  | 3 => [9, 10, 34, 57, 60]
  | 4 => [1, 4, 6, 34, 60]
  | _ => [0, 34]
theorem leftSignature_index0 : ∀ d : Fin 6, ∀ row : List State, leftSignature (direction d) (samples0 d) (literalDomain.zip row) = indexSignature (leftIndices0 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,0), patchState (literalDomain.zip row) (-4,4), patchState (literalDomain.zip row) (0,-4), patchState (literalDomain.zip row) (3,-4), patchState (literalDomain.zip row) (3,-3), patchState (literalDomain.zip row) (3,0)] = encode [(row[0]?).getD (0,0), (row[4]?).getD (0,0), (row[26]?).getD (0,0), (row[50]?).getD (0,0), (row[51]?).getD (0,0), (row[54]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup4 row, indexedLookup26 row, indexedLookup50 row, indexedLookup51 row, indexedLookup54 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,-1), patchState (literalDomain.zip row) (0,-4), patchState (literalDomain.zip row) (3,0), patchState (literalDomain.zip row) (4,-4), patchState (literalDomain.zip row) (4,-1)] = encode [(row[5]?).getD (0,0), (row[26]?).getD (0,0), (row[54]?).getD (0,0), (row[56]?).getD (0,0), (row[59]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup26 row, indexedLookup54 row, indexedLookup56 row, indexedLookup59 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (0,3), patchState (literalDomain.zip row) (1,-4), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (4,-4), patchState (literalDomain.zip row) (4,0)] = encode [(row[33]?).getD (0,0), (row[35]?).getD (0,0), (row[42]?).getD (0,0), (row[56]?).getD (0,0), (row[60]?).getD (0,0)]
    rw [indexedLookup33 row, indexedLookup35 row, indexedLookup42 row, indexedLookup56 row, indexedLookup60 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,3), patchState (literalDomain.zip row) (-3,4), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (4,-3), patchState (literalDomain.zip row) (4,0)] = encode [(row[9]?).getD (0,0), (row[10]?).getD (0,0), (row[34]?).getD (0,0), (row[57]?).getD (0,0), (row[60]?).getD (0,0)]
    rw [indexedLookup9 row, indexedLookup10 row, indexedLookup34 row, indexedLookup57 row, indexedLookup60 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,1), patchState (literalDomain.zip row) (-4,4), patchState (literalDomain.zip row) (-3,0), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (4,0)] = encode [(row[1]?).getD (0,0), (row[4]?).getD (0,0), (row[6]?).getD (0,0), (row[34]?).getD (0,0), (row[60]?).getD (0,0)]
    rw [indexedLookup1 row, indexedLookup4 row, indexedLookup6 row, indexedLookup34 row, indexedLookup60 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,0), patchState (literalDomain.zip row) (0,4)] = encode [(row[0]?).getD (0,0), (row[34]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup34 row]
def rightIndices0 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [6, 10, 35, 56, 57, 60]
  | 1 => [6, 27, 55, 57, 60]
  | 2 => [25, 27, 34, 51, 55]
  | 3 => [3, 4, 25, 51, 54]
  | 4 => [0, 3, 5, 33, 59]
  | _ => [5, 42]
theorem rightSignature_index0 : ∀ d : Fin 6, ∀ row : List State, rightSignature (samples0 d) (literalDomain.zip row) = indexSignature (rightIndices0 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,0), patchState (literalDomain.zip row) (-3,4), patchState (literalDomain.zip row) (1,-4), patchState (literalDomain.zip row) (4,-4), patchState (literalDomain.zip row) (4,-3), patchState (literalDomain.zip row) (4,0)] = encode [(row[6]?).getD (0,0), (row[10]?).getD (0,0), (row[35]?).getD (0,0), (row[56]?).getD (0,0), (row[57]?).getD (0,0), (row[60]?).getD (0,0)]
    rw [indexedLookup6 row, indexedLookup10 row, indexedLookup35 row, indexedLookup56 row, indexedLookup57 row, indexedLookup60 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,0), patchState (literalDomain.zip row) (0,-3), patchState (literalDomain.zip row) (3,1), patchState (literalDomain.zip row) (4,-3), patchState (literalDomain.zip row) (4,0)] = encode [(row[6]?).getD (0,0), (row[27]?).getD (0,0), (row[55]?).getD (0,0), (row[57]?).getD (0,0), (row[60]?).getD (0,0)]
    rw [indexedLookup6 row, indexedLookup27 row, indexedLookup55 row, indexedLookup57 row, indexedLookup60 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-1,4), patchState (literalDomain.zip row) (0,-3), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (3,-3), patchState (literalDomain.zip row) (3,1)] = encode [(row[25]?).getD (0,0), (row[27]?).getD (0,0), (row[34]?).getD (0,0), (row[51]?).getD (0,0), (row[55]?).getD (0,0)]
    rw [indexedLookup25 row, indexedLookup27 row, indexedLookup34 row, indexedLookup51 row, indexedLookup55 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,3), patchState (literalDomain.zip row) (-4,4), patchState (literalDomain.zip row) (-1,4), patchState (literalDomain.zip row) (3,-3), patchState (literalDomain.zip row) (3,0)] = encode [(row[3]?).getD (0,0), (row[4]?).getD (0,0), (row[25]?).getD (0,0), (row[51]?).getD (0,0), (row[54]?).getD (0,0)]
    rw [indexedLookup3 row, indexedLookup4 row, indexedLookup25 row, indexedLookup51 row, indexedLookup54 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,0), patchState (literalDomain.zip row) (-4,3), patchState (literalDomain.zip row) (-3,-1), patchState (literalDomain.zip row) (0,3), patchState (literalDomain.zip row) (4,-1)] = encode [(row[0]?).getD (0,0), (row[3]?).getD (0,0), (row[5]?).getD (0,0), (row[33]?).getD (0,0), (row[59]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup3 row, indexedLookup5 row, indexedLookup33 row, indexedLookup59 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,-1), patchState (literalDomain.zip row) (1,3)] = encode [(row[5]?).getD (0,0), (row[42]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup42 row]

end SpectreFinite.HexSearch.RadiusFourPruning
