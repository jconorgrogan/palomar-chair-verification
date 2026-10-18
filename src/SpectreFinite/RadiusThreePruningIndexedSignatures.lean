module

public import SpectreFinite.LargerWindowIndexedPruning
public import SpectreFinite.RadiusThreeRowProjection
public import SpectreFinite.RadiusThreePruningLiteralDomain
public import SpectreFinite.RadiusThreePruningGeometry

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThreePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem indexedLookup0 (row : List State) : patchState (literalDomain.zip row) (-3,0) = (row[0]?).getD (0,0) := patchState_zip_index literalDomain row (-3,0) 0 (by decide) (by decide)
theorem indexedLookup1 (row : List State) : patchState (literalDomain.zip row) (-3,1) = (row[1]?).getD (0,0) := patchState_zip_index literalDomain row (-3,1) 1 (by decide) (by decide)
theorem indexedLookup2 (row : List State) : patchState (literalDomain.zip row) (-3,2) = (row[2]?).getD (0,0) := patchState_zip_index literalDomain row (-3,2) 2 (by decide) (by decide)
theorem indexedLookup3 (row : List State) : patchState (literalDomain.zip row) (-3,3) = (row[3]?).getD (0,0) := patchState_zip_index literalDomain row (-3,3) 3 (by decide) (by decide)
theorem indexedLookup4 (row : List State) : patchState (literalDomain.zip row) (-2,-1) = (row[4]?).getD (0,0) := patchState_zip_index literalDomain row (-2,-1) 4 (by decide) (by decide)
theorem indexedLookup5 (row : List State) : patchState (literalDomain.zip row) (-2,0) = (row[5]?).getD (0,0) := patchState_zip_index literalDomain row (-2,0) 5 (by decide) (by decide)
theorem indexedLookup7 (row : List State) : patchState (literalDomain.zip row) (-2,2) = (row[7]?).getD (0,0) := patchState_zip_index literalDomain row (-2,2) 7 (by decide) (by decide)
theorem indexedLookup8 (row : List State) : patchState (literalDomain.zip row) (-2,3) = (row[8]?).getD (0,0) := patchState_zip_index literalDomain row (-2,3) 8 (by decide) (by decide)
theorem indexedLookup9 (row : List State) : patchState (literalDomain.zip row) (-1,-2) = (row[9]?).getD (0,0) := patchState_zip_index literalDomain row (-1,-2) 9 (by decide) (by decide)
theorem indexedLookup10 (row : List State) : patchState (literalDomain.zip row) (-1,-1) = (row[10]?).getD (0,0) := patchState_zip_index literalDomain row (-1,-1) 10 (by decide) (by decide)
theorem indexedLookup12 (row : List State) : patchState (literalDomain.zip row) (-1,1) = (row[12]?).getD (0,0) := patchState_zip_index literalDomain row (-1,1) 12 (by decide) (by decide)
theorem indexedLookup13 (row : List State) : patchState (literalDomain.zip row) (-1,2) = (row[13]?).getD (0,0) := patchState_zip_index literalDomain row (-1,2) 13 (by decide) (by decide)
theorem indexedLookup14 (row : List State) : patchState (literalDomain.zip row) (-1,3) = (row[14]?).getD (0,0) := patchState_zip_index literalDomain row (-1,3) 14 (by decide) (by decide)
theorem indexedLookup15 (row : List State) : patchState (literalDomain.zip row) (0,-3) = (row[15]?).getD (0,0) := patchState_zip_index literalDomain row (0,-3) 15 (by decide) (by decide)
theorem indexedLookup16 (row : List State) : patchState (literalDomain.zip row) (0,-2) = (row[16]?).getD (0,0) := patchState_zip_index literalDomain row (0,-2) 16 (by decide) (by decide)
theorem indexedLookup17 (row : List State) : patchState (literalDomain.zip row) (0,-1) = (row[17]?).getD (0,0) := patchState_zip_index literalDomain row (0,-1) 17 (by decide) (by decide)
theorem indexedLookup18 (row : List State) : patchState (literalDomain.zip row) (0,0) = (row[18]?).getD (0,0) := patchState_zip_index literalDomain row (0,0) 18 (by decide) (by decide)
theorem indexedLookup20 (row : List State) : patchState (literalDomain.zip row) (0,2) = (row[20]?).getD (0,0) := patchState_zip_index literalDomain row (0,2) 20 (by decide) (by decide)
theorem indexedLookup21 (row : List State) : patchState (literalDomain.zip row) (0,3) = (row[21]?).getD (0,0) := patchState_zip_index literalDomain row (0,3) 21 (by decide) (by decide)
theorem indexedLookup22 (row : List State) : patchState (literalDomain.zip row) (1,-3) = (row[22]?).getD (0,0) := patchState_zip_index literalDomain row (1,-3) 22 (by decide) (by decide)
theorem indexedLookup23 (row : List State) : patchState (literalDomain.zip row) (1,-2) = (row[23]?).getD (0,0) := patchState_zip_index literalDomain row (1,-2) 23 (by decide) (by decide)
theorem indexedLookup25 (row : List State) : patchState (literalDomain.zip row) (1,0) = (row[25]?).getD (0,0) := patchState_zip_index literalDomain row (1,0) 25 (by decide) (by decide)
theorem indexedLookup27 (row : List State) : patchState (literalDomain.zip row) (1,2) = (row[27]?).getD (0,0) := patchState_zip_index literalDomain row (1,2) 27 (by decide) (by decide)
theorem indexedLookup28 (row : List State) : patchState (literalDomain.zip row) (2,-3) = (row[28]?).getD (0,0) := patchState_zip_index literalDomain row (2,-3) 28 (by decide) (by decide)
theorem indexedLookup29 (row : List State) : patchState (literalDomain.zip row) (2,-2) = (row[29]?).getD (0,0) := patchState_zip_index literalDomain row (2,-2) 29 (by decide) (by decide)
theorem indexedLookup30 (row : List State) : patchState (literalDomain.zip row) (2,-1) = (row[30]?).getD (0,0) := patchState_zip_index literalDomain row (2,-1) 30 (by decide) (by decide)
theorem indexedLookup31 (row : List State) : patchState (literalDomain.zip row) (2,0) = (row[31]?).getD (0,0) := patchState_zip_index literalDomain row (2,0) 31 (by decide) (by decide)
theorem indexedLookup32 (row : List State) : patchState (literalDomain.zip row) (2,1) = (row[32]?).getD (0,0) := patchState_zip_index literalDomain row (2,1) 32 (by decide) (by decide)
theorem indexedLookup33 (row : List State) : patchState (literalDomain.zip row) (3,-3) = (row[33]?).getD (0,0) := patchState_zip_index literalDomain row (3,-3) 33 (by decide) (by decide)
theorem indexedLookup34 (row : List State) : patchState (literalDomain.zip row) (3,-2) = (row[34]?).getD (0,0) := patchState_zip_index literalDomain row (3,-2) 34 (by decide) (by decide)
theorem indexedLookup35 (row : List State) : patchState (literalDomain.zip row) (3,-1) = (row[35]?).getD (0,0) := patchState_zip_index literalDomain row (3,-1) 35 (by decide) (by decide)
theorem indexedLookup36 (row : List State) : patchState (literalDomain.zip row) (3,0) = (row[36]?).getD (0,0) := patchState_zip_index literalDomain row (3,0) 36 (by decide) (by decide)
def leftIndices0 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [3, 4, 28, 31]
  | 1 => [0, 22, 34, 35]
  | 2 => [15, 27, 34, 36]
  | 3 => [8, 27, 33, 36]
  | 4 => [1, 14, 18, 36]
  | _ => [5, 8, 9, 21]
theorem leftSignature_index0 : ∀ d : Fin 6, ∀ row : List State, leftSignature (direction d) (samples0 d) (literalDomain.zip row) = indexSignature (leftIndices0 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,3), patchState (literalDomain.zip row) (-2,-1), patchState (literalDomain.zip row) (2,-3), patchState (literalDomain.zip row) (2,0)] = encode [(row[3]?).getD (0,0), (row[4]?).getD (0,0), (row[28]?).getD (0,0), (row[31]?).getD (0,0)]
    rw [indexedLookup3 row, indexedLookup4 row, indexedLookup28 row, indexedLookup31 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,0), patchState (literalDomain.zip row) (1,-3), patchState (literalDomain.zip row) (3,-2), patchState (literalDomain.zip row) (3,-1)] = encode [(row[0]?).getD (0,0), (row[22]?).getD (0,0), (row[34]?).getD (0,0), (row[35]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup22 row, indexedLookup34 row, indexedLookup35 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (0,-3), patchState (literalDomain.zip row) (1,2), patchState (literalDomain.zip row) (3,-2), patchState (literalDomain.zip row) (3,0)] = encode [(row[15]?).getD (0,0), (row[27]?).getD (0,0), (row[34]?).getD (0,0), (row[36]?).getD (0,0)]
    rw [indexedLookup15 row, indexedLookup27 row, indexedLookup34 row, indexedLookup36 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,3), patchState (literalDomain.zip row) (1,2), patchState (literalDomain.zip row) (3,-3), patchState (literalDomain.zip row) (3,0)] = encode [(row[8]?).getD (0,0), (row[27]?).getD (0,0), (row[33]?).getD (0,0), (row[36]?).getD (0,0)]
    rw [indexedLookup8 row, indexedLookup27 row, indexedLookup33 row, indexedLookup36 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,1), patchState (literalDomain.zip row) (-1,3), patchState (literalDomain.zip row) (0,0), patchState (literalDomain.zip row) (3,0)] = encode [(row[1]?).getD (0,0), (row[14]?).getD (0,0), (row[18]?).getD (0,0), (row[36]?).getD (0,0)]
    rw [indexedLookup1 row, indexedLookup14 row, indexedLookup18 row, indexedLookup36 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,0), patchState (literalDomain.zip row) (-2,3), patchState (literalDomain.zip row) (-1,-2), patchState (literalDomain.zip row) (0,3)] = encode [(row[5]?).getD (0,0), (row[8]?).getD (0,0), (row[9]?).getD (0,0), (row[21]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup8 row, indexedLookup9 row, indexedLookup21 row]
def rightIndices0 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [8, 10, 33, 36]
  | 1 => [1, 23, 35, 36]
  | 2 => [9, 21, 30, 32]
  | 3 => [3, 20, 28, 31]
  | 4 => [0, 13, 17, 35]
  | _ => [10, 13, 15, 27]
theorem rightSignature_index0 : ∀ d : Fin 6, ∀ row : List State, rightSignature (samples0 d) (literalDomain.zip row) = indexSignature (rightIndices0 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,3), patchState (literalDomain.zip row) (-1,-1), patchState (literalDomain.zip row) (3,-3), patchState (literalDomain.zip row) (3,0)] = encode [(row[8]?).getD (0,0), (row[10]?).getD (0,0), (row[33]?).getD (0,0), (row[36]?).getD (0,0)]
    rw [indexedLookup8 row, indexedLookup10 row, indexedLookup33 row, indexedLookup36 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,1), patchState (literalDomain.zip row) (1,-2), patchState (literalDomain.zip row) (3,-1), patchState (literalDomain.zip row) (3,0)] = encode [(row[1]?).getD (0,0), (row[23]?).getD (0,0), (row[35]?).getD (0,0), (row[36]?).getD (0,0)]
    rw [indexedLookup1 row, indexedLookup23 row, indexedLookup35 row, indexedLookup36 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-1,-2), patchState (literalDomain.zip row) (0,3), patchState (literalDomain.zip row) (2,-1), patchState (literalDomain.zip row) (2,1)] = encode [(row[9]?).getD (0,0), (row[21]?).getD (0,0), (row[30]?).getD (0,0), (row[32]?).getD (0,0)]
    rw [indexedLookup9 row, indexedLookup21 row, indexedLookup30 row, indexedLookup32 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,3), patchState (literalDomain.zip row) (0,2), patchState (literalDomain.zip row) (2,-3), patchState (literalDomain.zip row) (2,0)] = encode [(row[3]?).getD (0,0), (row[20]?).getD (0,0), (row[28]?).getD (0,0), (row[31]?).getD (0,0)]
    rw [indexedLookup3 row, indexedLookup20 row, indexedLookup28 row, indexedLookup31 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,0), patchState (literalDomain.zip row) (-1,2), patchState (literalDomain.zip row) (0,-1), patchState (literalDomain.zip row) (3,-1)] = encode [(row[0]?).getD (0,0), (row[13]?).getD (0,0), (row[17]?).getD (0,0), (row[35]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup13 row, indexedLookup17 row, indexedLookup35 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-1,-1), patchState (literalDomain.zip row) (-1,2), patchState (literalDomain.zip row) (0,-3), patchState (literalDomain.zip row) (1,2)] = encode [(row[10]?).getD (0,0), (row[13]?).getD (0,0), (row[15]?).getD (0,0), (row[27]?).getD (0,0)]
    rw [indexedLookup10 row, indexedLookup13 row, indexedLookup15 row, indexedLookup27 row]
def leftIndices1 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [0, 3, 15, 29, 31]
  | 1 => [9, 12, 15, 33]
  | 2 => [28, 32, 33, 36]
  | 3 => [21, 25, 35, 36]
  | 4 => [3, 21, 30, 36]
  | _ => [1, 21, 32]
theorem leftSignature_index1 : ∀ d : Fin 6, ∀ row : List State, leftSignature (direction d) (samples1 d) (literalDomain.zip row) = indexSignature (leftIndices1 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,0), patchState (literalDomain.zip row) (-3,3), patchState (literalDomain.zip row) (0,-3), patchState (literalDomain.zip row) (2,-2), patchState (literalDomain.zip row) (2,0)] = encode [(row[0]?).getD (0,0), (row[3]?).getD (0,0), (row[15]?).getD (0,0), (row[29]?).getD (0,0), (row[31]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup3 row, indexedLookup15 row, indexedLookup29 row, indexedLookup31 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-1,-2), patchState (literalDomain.zip row) (-1,1), patchState (literalDomain.zip row) (0,-3), patchState (literalDomain.zip row) (3,-3)] = encode [(row[9]?).getD (0,0), (row[12]?).getD (0,0), (row[15]?).getD (0,0), (row[33]?).getD (0,0)]
    rw [indexedLookup9 row, indexedLookup12 row, indexedLookup15 row, indexedLookup33 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (2,-3), patchState (literalDomain.zip row) (2,1), patchState (literalDomain.zip row) (3,-3), patchState (literalDomain.zip row) (3,0)] = encode [(row[28]?).getD (0,0), (row[32]?).getD (0,0), (row[33]?).getD (0,0), (row[36]?).getD (0,0)]
    rw [indexedLookup28 row, indexedLookup32 row, indexedLookup33 row, indexedLookup36 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (0,3), patchState (literalDomain.zip row) (1,0), patchState (literalDomain.zip row) (3,-1), patchState (literalDomain.zip row) (3,0)] = encode [(row[21]?).getD (0,0), (row[25]?).getD (0,0), (row[35]?).getD (0,0), (row[36]?).getD (0,0)]
    rw [indexedLookup21 row, indexedLookup25 row, indexedLookup35 row, indexedLookup36 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,3), patchState (literalDomain.zip row) (0,3), patchState (literalDomain.zip row) (2,-1), patchState (literalDomain.zip row) (3,0)] = encode [(row[3]?).getD (0,0), (row[21]?).getD (0,0), (row[30]?).getD (0,0), (row[36]?).getD (0,0)]
    rw [indexedLookup3 row, indexedLookup21 row, indexedLookup30 row, indexedLookup36 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,1), patchState (literalDomain.zip row) (0,3), patchState (literalDomain.zip row) (2,1)] = encode [(row[1]?).getD (0,0), (row[21]?).getD (0,0), (row[32]?).getD (0,0)]
    rw [indexedLookup1 row, indexedLookup21 row, indexedLookup32 row]
def rightIndices1 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [5, 8, 22, 34, 36]
  | 1 => [10, 13, 16, 34]
  | 2 => [23, 27, 29, 32]
  | 3 => [14, 18, 30, 31]
  | 4 => [2, 20, 29, 35]
  | _ => [5, 27, 36]
theorem rightSignature_index1 : ∀ d : Fin 6, ∀ row : List State, rightSignature (samples1 d) (literalDomain.zip row) = indexSignature (rightIndices1 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,0), patchState (literalDomain.zip row) (-2,3), patchState (literalDomain.zip row) (1,-3), patchState (literalDomain.zip row) (3,-2), patchState (literalDomain.zip row) (3,0)] = encode [(row[5]?).getD (0,0), (row[8]?).getD (0,0), (row[22]?).getD (0,0), (row[34]?).getD (0,0), (row[36]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup8 row, indexedLookup22 row, indexedLookup34 row, indexedLookup36 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-1,-1), patchState (literalDomain.zip row) (-1,2), patchState (literalDomain.zip row) (0,-2), patchState (literalDomain.zip row) (3,-2)] = encode [(row[10]?).getD (0,0), (row[13]?).getD (0,0), (row[16]?).getD (0,0), (row[34]?).getD (0,0)]
    rw [indexedLookup10 row, indexedLookup13 row, indexedLookup16 row, indexedLookup34 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (1,-2), patchState (literalDomain.zip row) (1,2), patchState (literalDomain.zip row) (2,-2), patchState (literalDomain.zip row) (2,1)] = encode [(row[23]?).getD (0,0), (row[27]?).getD (0,0), (row[29]?).getD (0,0), (row[32]?).getD (0,0)]
    rw [indexedLookup23 row, indexedLookup27 row, indexedLookup29 row, indexedLookup32 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-1,3), patchState (literalDomain.zip row) (0,0), patchState (literalDomain.zip row) (2,-1), patchState (literalDomain.zip row) (2,0)] = encode [(row[14]?).getD (0,0), (row[18]?).getD (0,0), (row[30]?).getD (0,0), (row[31]?).getD (0,0)]
    rw [indexedLookup14 row, indexedLookup18 row, indexedLookup30 row, indexedLookup31 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,2), patchState (literalDomain.zip row) (0,2), patchState (literalDomain.zip row) (2,-2), patchState (literalDomain.zip row) (3,-1)] = encode [(row[2]?).getD (0,0), (row[20]?).getD (0,0), (row[29]?).getD (0,0), (row[35]?).getD (0,0)]
    rw [indexedLookup2 row, indexedLookup20 row, indexedLookup29 row, indexedLookup35 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,0), patchState (literalDomain.zip row) (1,2), patchState (literalDomain.zip row) (3,0)] = encode [(row[5]?).getD (0,0), (row[27]?).getD (0,0), (row[36]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup27 row, indexedLookup36 row]
def leftIndices2 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [2, 14, 15, 28, 31]
  | 1 => [31, 34]
  | 2 => [32, 33]
  | 3 => []
  | 4 => []
  | _ => []
theorem leftSignature_index2 : ∀ d : Fin 6, ∀ row : List State, leftSignature (direction d) (samples2 d) (literalDomain.zip row) = indexSignature (leftIndices2 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,2), patchState (literalDomain.zip row) (-1,3), patchState (literalDomain.zip row) (0,-3), patchState (literalDomain.zip row) (2,-3), patchState (literalDomain.zip row) (2,0)] = encode [(row[2]?).getD (0,0), (row[14]?).getD (0,0), (row[15]?).getD (0,0), (row[28]?).getD (0,0), (row[31]?).getD (0,0)]
    rw [indexedLookup2 row, indexedLookup14 row, indexedLookup15 row, indexedLookup28 row, indexedLookup31 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (2,0), patchState (literalDomain.zip row) (3,-2)] = encode [(row[31]?).getD (0,0), (row[34]?).getD (0,0)]
    rw [indexedLookup31 row, indexedLookup34 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (2,1), patchState (literalDomain.zip row) (3,-3)] = encode [(row[32]?).getD (0,0), (row[33]?).getD (0,0)]
    rw [indexedLookup32 row, indexedLookup33 row]
  · intro row
    rfl
  · intro row
    rfl
  · intro row
    rfl
def rightIndices2 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [7, 21, 22, 33, 36]
  | 1 => [32, 35]
  | 2 => [27, 29]
  | 3 => []
  | 4 => []
  | _ => []
theorem rightSignature_index2 : ∀ d : Fin 6, ∀ row : List State, rightSignature (samples2 d) (literalDomain.zip row) = indexSignature (rightIndices2 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,2), patchState (literalDomain.zip row) (0,3), patchState (literalDomain.zip row) (1,-3), patchState (literalDomain.zip row) (3,-3), patchState (literalDomain.zip row) (3,0)] = encode [(row[7]?).getD (0,0), (row[21]?).getD (0,0), (row[22]?).getD (0,0), (row[33]?).getD (0,0), (row[36]?).getD (0,0)]
    rw [indexedLookup7 row, indexedLookup21 row, indexedLookup22 row, indexedLookup33 row, indexedLookup36 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (2,1), patchState (literalDomain.zip row) (3,-1)] = encode [(row[32]?).getD (0,0), (row[35]?).getD (0,0)]
    rw [indexedLookup32 row, indexedLookup35 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (1,2), patchState (literalDomain.zip row) (2,-2)] = encode [(row[27]?).getD (0,0), (row[29]?).getD (0,0)]
    rw [indexedLookup27 row, indexedLookup29 row]
  · intro row
    rfl
  · intro row
    rfl
  · intro row
    rfl

end SpectreFinite.HexSearch.RadiusThreePruning
