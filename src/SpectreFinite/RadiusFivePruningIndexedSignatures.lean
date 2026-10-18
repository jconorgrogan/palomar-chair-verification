module

public import SpectreFinite.LargerWindowIndexedPruning
public import SpectreFinite.RadiusThreeRowProjection
public import SpectreFinite.RadiusFivePruningLiteralDomain
public import SpectreFinite.RadiusFivePruningGeometry

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
open LargerWindowPruning
open SignaturePruning (KeyTree)
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem indexedLookup0 (row : List State) : patchState (literalDomain.zip row) (-5,0) = (row[0]?).getD (0,0) := patchState_zip_index literalDomain row (-5,0) 0 (by decide) (by decide)
theorem indexedLookup1 (row : List State) : patchState (literalDomain.zip row) (-5,1) = (row[1]?).getD (0,0) := patchState_zip_index literalDomain row (-5,1) 1 (by decide) (by decide)
theorem indexedLookup2 (row : List State) : patchState (literalDomain.zip row) (-5,2) = (row[2]?).getD (0,0) := patchState_zip_index literalDomain row (-5,2) 2 (by decide) (by decide)
theorem indexedLookup3 (row : List State) : patchState (literalDomain.zip row) (-5,3) = (row[3]?).getD (0,0) := patchState_zip_index literalDomain row (-5,3) 3 (by decide) (by decide)
theorem indexedLookup4 (row : List State) : patchState (literalDomain.zip row) (-5,4) = (row[4]?).getD (0,0) := patchState_zip_index literalDomain row (-5,4) 4 (by decide) (by decide)
theorem indexedLookup5 (row : List State) : patchState (literalDomain.zip row) (-5,5) = (row[5]?).getD (0,0) := patchState_zip_index literalDomain row (-5,5) 5 (by decide) (by decide)
theorem indexedLookup6 (row : List State) : patchState (literalDomain.zip row) (-4,-1) = (row[6]?).getD (0,0) := patchState_zip_index literalDomain row (-4,-1) 6 (by decide) (by decide)
theorem indexedLookup7 (row : List State) : patchState (literalDomain.zip row) (-4,0) = (row[7]?).getD (0,0) := patchState_zip_index literalDomain row (-4,0) 7 (by decide) (by decide)
theorem indexedLookup8 (row : List State) : patchState (literalDomain.zip row) (-4,1) = (row[8]?).getD (0,0) := patchState_zip_index literalDomain row (-4,1) 8 (by decide) (by decide)
theorem indexedLookup9 (row : List State) : patchState (literalDomain.zip row) (-4,2) = (row[9]?).getD (0,0) := patchState_zip_index literalDomain row (-4,2) 9 (by decide) (by decide)
theorem indexedLookup10 (row : List State) : patchState (literalDomain.zip row) (-4,3) = (row[10]?).getD (0,0) := patchState_zip_index literalDomain row (-4,3) 10 (by decide) (by decide)
theorem indexedLookup11 (row : List State) : patchState (literalDomain.zip row) (-4,4) = (row[11]?).getD (0,0) := patchState_zip_index literalDomain row (-4,4) 11 (by decide) (by decide)
theorem indexedLookup12 (row : List State) : patchState (literalDomain.zip row) (-4,5) = (row[12]?).getD (0,0) := patchState_zip_index literalDomain row (-4,5) 12 (by decide) (by decide)
theorem indexedLookup13 (row : List State) : patchState (literalDomain.zip row) (-3,-2) = (row[13]?).getD (0,0) := patchState_zip_index literalDomain row (-3,-2) 13 (by decide) (by decide)
theorem indexedLookup14 (row : List State) : patchState (literalDomain.zip row) (-3,-1) = (row[14]?).getD (0,0) := patchState_zip_index literalDomain row (-3,-1) 14 (by decide) (by decide)
theorem indexedLookup15 (row : List State) : patchState (literalDomain.zip row) (-3,0) = (row[15]?).getD (0,0) := patchState_zip_index literalDomain row (-3,0) 15 (by decide) (by decide)
theorem indexedLookup16 (row : List State) : patchState (literalDomain.zip row) (-3,1) = (row[16]?).getD (0,0) := patchState_zip_index literalDomain row (-3,1) 16 (by decide) (by decide)
theorem indexedLookup17 (row : List State) : patchState (literalDomain.zip row) (-3,2) = (row[17]?).getD (0,0) := patchState_zip_index literalDomain row (-3,2) 17 (by decide) (by decide)
theorem indexedLookup19 (row : List State) : patchState (literalDomain.zip row) (-3,4) = (row[19]?).getD (0,0) := patchState_zip_index literalDomain row (-3,4) 19 (by decide) (by decide)
theorem indexedLookup20 (row : List State) : patchState (literalDomain.zip row) (-3,5) = (row[20]?).getD (0,0) := patchState_zip_index literalDomain row (-3,5) 20 (by decide) (by decide)
theorem indexedLookup21 (row : List State) : patchState (literalDomain.zip row) (-2,-3) = (row[21]?).getD (0,0) := patchState_zip_index literalDomain row (-2,-3) 21 (by decide) (by decide)
theorem indexedLookup22 (row : List State) : patchState (literalDomain.zip row) (-2,-2) = (row[22]?).getD (0,0) := patchState_zip_index literalDomain row (-2,-2) 22 (by decide) (by decide)
theorem indexedLookup27 (row : List State) : patchState (literalDomain.zip row) (-2,3) = (row[27]?).getD (0,0) := patchState_zip_index literalDomain row (-2,3) 27 (by decide) (by decide)
theorem indexedLookup28 (row : List State) : patchState (literalDomain.zip row) (-2,4) = (row[28]?).getD (0,0) := patchState_zip_index literalDomain row (-2,4) 28 (by decide) (by decide)
theorem indexedLookup29 (row : List State) : patchState (literalDomain.zip row) (-2,5) = (row[29]?).getD (0,0) := patchState_zip_index literalDomain row (-2,5) 29 (by decide) (by decide)
theorem indexedLookup30 (row : List State) : patchState (literalDomain.zip row) (-1,-4) = (row[30]?).getD (0,0) := patchState_zip_index literalDomain row (-1,-4) 30 (by decide) (by decide)
theorem indexedLookup31 (row : List State) : patchState (literalDomain.zip row) (-1,-3) = (row[31]?).getD (0,0) := patchState_zip_index literalDomain row (-1,-3) 31 (by decide) (by decide)
theorem indexedLookup36 (row : List State) : patchState (literalDomain.zip row) (-1,2) = (row[36]?).getD (0,0) := patchState_zip_index literalDomain row (-1,2) 36 (by decide) (by decide)
theorem indexedLookup37 (row : List State) : patchState (literalDomain.zip row) (-1,3) = (row[37]?).getD (0,0) := patchState_zip_index literalDomain row (-1,3) 37 (by decide) (by decide)
theorem indexedLookup38 (row : List State) : patchState (literalDomain.zip row) (-1,4) = (row[38]?).getD (0,0) := patchState_zip_index literalDomain row (-1,4) 38 (by decide) (by decide)
theorem indexedLookup39 (row : List State) : patchState (literalDomain.zip row) (-1,5) = (row[39]?).getD (0,0) := patchState_zip_index literalDomain row (-1,5) 39 (by decide) (by decide)
theorem indexedLookup40 (row : List State) : patchState (literalDomain.zip row) (0,-5) = (row[40]?).getD (0,0) := patchState_zip_index literalDomain row (0,-5) 40 (by decide) (by decide)
theorem indexedLookup41 (row : List State) : patchState (literalDomain.zip row) (0,-4) = (row[41]?).getD (0,0) := patchState_zip_index literalDomain row (0,-4) 41 (by decide) (by decide)
theorem indexedLookup42 (row : List State) : patchState (literalDomain.zip row) (0,-3) = (row[42]?).getD (0,0) := patchState_zip_index literalDomain row (0,-3) 42 (by decide) (by decide)
theorem indexedLookup43 (row : List State) : patchState (literalDomain.zip row) (0,-2) = (row[43]?).getD (0,0) := patchState_zip_index literalDomain row (0,-2) 43 (by decide) (by decide)
theorem indexedLookup48 (row : List State) : patchState (literalDomain.zip row) (0,3) = (row[48]?).getD (0,0) := patchState_zip_index literalDomain row (0,3) 48 (by decide) (by decide)
theorem indexedLookup49 (row : List State) : patchState (literalDomain.zip row) (0,4) = (row[49]?).getD (0,0) := patchState_zip_index literalDomain row (0,4) 49 (by decide) (by decide)
theorem indexedLookup50 (row : List State) : patchState (literalDomain.zip row) (0,5) = (row[50]?).getD (0,0) := patchState_zip_index literalDomain row (0,5) 50 (by decide) (by decide)
theorem indexedLookup51 (row : List State) : patchState (literalDomain.zip row) (1,-5) = (row[51]?).getD (0,0) := patchState_zip_index literalDomain row (1,-5) 51 (by decide) (by decide)
theorem indexedLookup52 (row : List State) : patchState (literalDomain.zip row) (1,-4) = (row[52]?).getD (0,0) := patchState_zip_index literalDomain row (1,-4) 52 (by decide) (by decide)
theorem indexedLookup53 (row : List State) : patchState (literalDomain.zip row) (1,-3) = (row[53]?).getD (0,0) := patchState_zip_index literalDomain row (1,-3) 53 (by decide) (by decide)
theorem indexedLookup54 (row : List State) : patchState (literalDomain.zip row) (1,-2) = (row[54]?).getD (0,0) := patchState_zip_index literalDomain row (1,-2) 54 (by decide) (by decide)
theorem indexedLookup57 (row : List State) : patchState (literalDomain.zip row) (1,1) = (row[57]?).getD (0,0) := patchState_zip_index literalDomain row (1,1) 57 (by decide) (by decide)
theorem indexedLookup58 (row : List State) : patchState (literalDomain.zip row) (1,2) = (row[58]?).getD (0,0) := patchState_zip_index literalDomain row (1,2) 58 (by decide) (by decide)
theorem indexedLookup59 (row : List State) : patchState (literalDomain.zip row) (1,3) = (row[59]?).getD (0,0) := patchState_zip_index literalDomain row (1,3) 59 (by decide) (by decide)
theorem indexedLookup60 (row : List State) : patchState (literalDomain.zip row) (1,4) = (row[60]?).getD (0,0) := patchState_zip_index literalDomain row (1,4) 60 (by decide) (by decide)
theorem indexedLookup61 (row : List State) : patchState (literalDomain.zip row) (2,-5) = (row[61]?).getD (0,0) := patchState_zip_index literalDomain row (2,-5) 61 (by decide) (by decide)
theorem indexedLookup62 (row : List State) : patchState (literalDomain.zip row) (2,-4) = (row[62]?).getD (0,0) := patchState_zip_index literalDomain row (2,-4) 62 (by decide) (by decide)
theorem indexedLookup63 (row : List State) : patchState (literalDomain.zip row) (2,-3) = (row[63]?).getD (0,0) := patchState_zip_index literalDomain row (2,-3) 63 (by decide) (by decide)
theorem indexedLookup64 (row : List State) : patchState (literalDomain.zip row) (2,-2) = (row[64]?).getD (0,0) := patchState_zip_index literalDomain row (2,-2) 64 (by decide) (by decide)
theorem indexedLookup66 (row : List State) : patchState (literalDomain.zip row) (2,0) = (row[66]?).getD (0,0) := patchState_zip_index literalDomain row (2,0) 66 (by decide) (by decide)
theorem indexedLookup67 (row : List State) : patchState (literalDomain.zip row) (2,1) = (row[67]?).getD (0,0) := patchState_zip_index literalDomain row (2,1) 67 (by decide) (by decide)
theorem indexedLookup68 (row : List State) : patchState (literalDomain.zip row) (2,2) = (row[68]?).getD (0,0) := patchState_zip_index literalDomain row (2,2) 68 (by decide) (by decide)
theorem indexedLookup69 (row : List State) : patchState (literalDomain.zip row) (2,3) = (row[69]?).getD (0,0) := patchState_zip_index literalDomain row (2,3) 69 (by decide) (by decide)
theorem indexedLookup70 (row : List State) : patchState (literalDomain.zip row) (3,-5) = (row[70]?).getD (0,0) := patchState_zip_index literalDomain row (3,-5) 70 (by decide) (by decide)
theorem indexedLookup71 (row : List State) : patchState (literalDomain.zip row) (3,-4) = (row[71]?).getD (0,0) := patchState_zip_index literalDomain row (3,-4) 71 (by decide) (by decide)
theorem indexedLookup72 (row : List State) : patchState (literalDomain.zip row) (3,-3) = (row[72]?).getD (0,0) := patchState_zip_index literalDomain row (3,-3) 72 (by decide) (by decide)
theorem indexedLookup73 (row : List State) : patchState (literalDomain.zip row) (3,-2) = (row[73]?).getD (0,0) := patchState_zip_index literalDomain row (3,-2) 73 (by decide) (by decide)
theorem indexedLookup76 (row : List State) : patchState (literalDomain.zip row) (3,1) = (row[76]?).getD (0,0) := patchState_zip_index literalDomain row (3,1) 76 (by decide) (by decide)
theorem indexedLookup77 (row : List State) : patchState (literalDomain.zip row) (3,2) = (row[77]?).getD (0,0) := patchState_zip_index literalDomain row (3,2) 77 (by decide) (by decide)
theorem indexedLookup78 (row : List State) : patchState (literalDomain.zip row) (4,-5) = (row[78]?).getD (0,0) := patchState_zip_index literalDomain row (4,-5) 78 (by decide) (by decide)
theorem indexedLookup79 (row : List State) : patchState (literalDomain.zip row) (4,-4) = (row[79]?).getD (0,0) := patchState_zip_index literalDomain row (4,-4) 79 (by decide) (by decide)
theorem indexedLookup80 (row : List State) : patchState (literalDomain.zip row) (4,-3) = (row[80]?).getD (0,0) := patchState_zip_index literalDomain row (4,-3) 80 (by decide) (by decide)
theorem indexedLookup81 (row : List State) : patchState (literalDomain.zip row) (4,-2) = (row[81]?).getD (0,0) := patchState_zip_index literalDomain row (4,-2) 81 (by decide) (by decide)
theorem indexedLookup82 (row : List State) : patchState (literalDomain.zip row) (4,-1) = (row[82]?).getD (0,0) := patchState_zip_index literalDomain row (4,-1) 82 (by decide) (by decide)
theorem indexedLookup83 (row : List State) : patchState (literalDomain.zip row) (4,0) = (row[83]?).getD (0,0) := patchState_zip_index literalDomain row (4,0) 83 (by decide) (by decide)
theorem indexedLookup84 (row : List State) : patchState (literalDomain.zip row) (4,1) = (row[84]?).getD (0,0) := patchState_zip_index literalDomain row (4,1) 84 (by decide) (by decide)
theorem indexedLookup85 (row : List State) : patchState (literalDomain.zip row) (5,-5) = (row[85]?).getD (0,0) := patchState_zip_index literalDomain row (5,-5) 85 (by decide) (by decide)
theorem indexedLookup86 (row : List State) : patchState (literalDomain.zip row) (5,-4) = (row[86]?).getD (0,0) := patchState_zip_index literalDomain row (5,-4) 86 (by decide) (by decide)
theorem indexedLookup87 (row : List State) : patchState (literalDomain.zip row) (5,-3) = (row[87]?).getD (0,0) := patchState_zip_index literalDomain row (5,-3) 87 (by decide) (by decide)
theorem indexedLookup88 (row : List State) : patchState (literalDomain.zip row) (5,-2) = (row[88]?).getD (0,0) := patchState_zip_index literalDomain row (5,-2) 88 (by decide) (by decide)
theorem indexedLookup89 (row : List State) : patchState (literalDomain.zip row) (5,-1) = (row[89]?).getD (0,0) := patchState_zip_index literalDomain row (5,-1) 89 (by decide) (by decide)
theorem indexedLookup90 (row : List State) : patchState (literalDomain.zip row) (5,0) = (row[90]?).getD (0,0) := patchState_zip_index literalDomain row (5,0) 90 (by decide) (by decide)
def leftIndices0 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [5, 20, 30, 48, 59, 76, 78, 83]
  | 1 => [1, 3, 21, 58, 85, 89]
  | 2 => [40, 60, 71, 90]
  | 3 => [12, 68, 78, 85, 87]
  | 4 => [1, 79, 84, 90]
  | _ => [30, 49, 60, 77, 84]
theorem leftSignature_index0 : ∀ d : Fin 6, ∀ row : List State, leftSignature (direction d) (samples0 d) (literalDomain.zip row) = indexSignature (leftIndices0 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (-3,5), patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (0,3), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (3,1), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (4,0)] = encode [(row[5]?).getD (0,0), (row[20]?).getD (0,0), (row[30]?).getD (0,0), (row[48]?).getD (0,0), (row[59]?).getD (0,0), (row[76]?).getD (0,0), (row[78]?).getD (0,0), (row[83]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup20 row, indexedLookup30 row, indexedLookup48 row, indexedLookup59 row, indexedLookup76 row, indexedLookup78 row, indexedLookup83 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,1), patchState (literalDomain.zip row) (-5,3), patchState (literalDomain.zip row) (-2,-3), patchState (literalDomain.zip row) (1,2), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,-1)] = encode [(row[1]?).getD (0,0), (row[3]?).getD (0,0), (row[21]?).getD (0,0), (row[58]?).getD (0,0), (row[85]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup1 row, indexedLookup3 row, indexedLookup21 row, indexedLookup58 row, indexedLookup85 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (3,-4), patchState (literalDomain.zip row) (5,0)] = encode [(row[40]?).getD (0,0), (row[60]?).getD (0,0), (row[71]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup40 row, indexedLookup60 row, indexedLookup71 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (2,2), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,-3)] = encode [(row[12]?).getD (0,0), (row[68]?).getD (0,0), (row[78]?).getD (0,0), (row[85]?).getD (0,0), (row[87]?).getD (0,0)]
    rw [indexedLookup12 row, indexedLookup68 row, indexedLookup78 row, indexedLookup85 row, indexedLookup87 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,1), patchState (literalDomain.zip row) (4,-4), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,0)] = encode [(row[1]?).getD (0,0), (row[79]?).getD (0,0), (row[84]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup1 row, indexedLookup79 row, indexedLookup84 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (3,2), patchState (literalDomain.zip row) (4,1)] = encode [(row[30]?).getD (0,0), (row[49]?).getD (0,0), (row[60]?).getD (0,0), (row[77]?).getD (0,0), (row[84]?).getD (0,0)]
    rw [indexedLookup30 row, indexedLookup49 row, indexedLookup60 row, indexedLookup77 row, indexedLookup84 row]
def rightIndices0 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [12, 29, 41, 59, 69, 84, 85, 90]
  | 1 => [2, 4, 22, 59, 86, 90]
  | 2 => [30, 50, 63, 84]
  | 3 => [5, 58, 70, 78, 80]
  | 4 => [0, 78, 83, 89]
  | _ => [40, 59, 69, 84, 90]
theorem rightSignature_index0 : ∀ d : Fin 6, ∀ row : List State, rightSignature (samples0 d) (literalDomain.zip row) = indexSignature (rightIndices0 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (-2,5), patchState (literalDomain.zip row) (0,-4), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,0)] = encode [(row[12]?).getD (0,0), (row[29]?).getD (0,0), (row[41]?).getD (0,0), (row[59]?).getD (0,0), (row[69]?).getD (0,0), (row[84]?).getD (0,0), (row[85]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup12 row, indexedLookup29 row, indexedLookup41 row, indexedLookup59 row, indexedLookup69 row, indexedLookup84 row, indexedLookup85 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,2), patchState (literalDomain.zip row) (-5,4), patchState (literalDomain.zip row) (-2,-2), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (5,-4), patchState (literalDomain.zip row) (5,0)] = encode [(row[2]?).getD (0,0), (row[4]?).getD (0,0), (row[22]?).getD (0,0), (row[59]?).getD (0,0), (row[86]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup2 row, indexedLookup4 row, indexedLookup22 row, indexedLookup59 row, indexedLookup86 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (2,-3), patchState (literalDomain.zip row) (4,1)] = encode [(row[30]?).getD (0,0), (row[50]?).getD (0,0), (row[63]?).getD (0,0), (row[84]?).getD (0,0)]
    rw [indexedLookup30 row, indexedLookup50 row, indexedLookup63 row, indexedLookup84 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (1,2), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (4,-3)] = encode [(row[5]?).getD (0,0), (row[58]?).getD (0,0), (row[70]?).getD (0,0), (row[78]?).getD (0,0), (row[80]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup58 row, indexedLookup70 row, indexedLookup78 row, indexedLookup80 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,0), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (4,0), patchState (literalDomain.zip row) (5,-1)] = encode [(row[0]?).getD (0,0), (row[78]?).getD (0,0), (row[83]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup78 row, indexedLookup83 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,0)] = encode [(row[40]?).getD (0,0), (row[59]?).getD (0,0), (row[69]?).getD (0,0), (row[84]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup40 row, indexedLookup59 row, indexedLookup69 row, indexedLookup84 row, indexedLookup90 row]
def leftIndices1 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [5, 20, 30, 48, 62, 78, 83]
  | 1 => [0, 2, 38, 78, 83, 87]
  | 2 => [16, 21, 40, 49, 77, 78, 90]
  | 3 => [17, 29, 52, 60, 70, 85, 89]
  | 4 => [3, 42, 60, 84, 86, 88, 90]
  | _ => [30, 39, 50, 69, 79, 84]
theorem leftSignature_index1 : ∀ d : Fin 6, ∀ row : List State, leftSignature (direction d) (samples1 d) (literalDomain.zip row) = indexSignature (leftIndices1 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (-3,5), patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (0,3), patchState (literalDomain.zip row) (2,-4), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (4,0)] = encode [(row[5]?).getD (0,0), (row[20]?).getD (0,0), (row[30]?).getD (0,0), (row[48]?).getD (0,0), (row[62]?).getD (0,0), (row[78]?).getD (0,0), (row[83]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup20 row, indexedLookup30 row, indexedLookup48 row, indexedLookup62 row, indexedLookup78 row, indexedLookup83 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,0), patchState (literalDomain.zip row) (-5,2), patchState (literalDomain.zip row) (-1,4), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (4,0), patchState (literalDomain.zip row) (5,-3)] = encode [(row[0]?).getD (0,0), (row[2]?).getD (0,0), (row[38]?).getD (0,0), (row[78]?).getD (0,0), (row[83]?).getD (0,0), (row[87]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup2 row, indexedLookup38 row, indexedLookup78 row, indexedLookup83 row, indexedLookup87 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,1), patchState (literalDomain.zip row) (-2,-3), patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (3,2), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (5,0)] = encode [(row[16]?).getD (0,0), (row[21]?).getD (0,0), (row[40]?).getD (0,0), (row[49]?).getD (0,0), (row[77]?).getD (0,0), (row[78]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup16 row, indexedLookup21 row, indexedLookup40 row, indexedLookup49 row, indexedLookup77 row, indexedLookup78 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,2), patchState (literalDomain.zip row) (-2,5), patchState (literalDomain.zip row) (1,-4), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,-1)] = encode [(row[17]?).getD (0,0), (row[29]?).getD (0,0), (row[52]?).getD (0,0), (row[60]?).getD (0,0), (row[70]?).getD (0,0), (row[85]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup17 row, indexedLookup29 row, indexedLookup52 row, indexedLookup60 row, indexedLookup70 row, indexedLookup85 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,3), patchState (literalDomain.zip row) (0,-3), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,-4), patchState (literalDomain.zip row) (5,-2), patchState (literalDomain.zip row) (5,0)] = encode [(row[3]?).getD (0,0), (row[42]?).getD (0,0), (row[60]?).getD (0,0), (row[84]?).getD (0,0), (row[86]?).getD (0,0), (row[88]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup3 row, indexedLookup42 row, indexedLookup60 row, indexedLookup84 row, indexedLookup86 row, indexedLookup88 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (4,-4), patchState (literalDomain.zip row) (4,1)] = encode [(row[30]?).getD (0,0), (row[39]?).getD (0,0), (row[50]?).getD (0,0), (row[69]?).getD (0,0), (row[79]?).getD (0,0), (row[84]?).getD (0,0)]
    rw [indexedLookup30 row, indexedLookup39 row, indexedLookup50 row, indexedLookup69 row, indexedLookup79 row, indexedLookup84 row]
def rightIndices1 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [12, 29, 41, 59, 71, 85, 90]
  | 1 => [1, 3, 39, 79, 84, 88]
  | 2 => [9, 13, 30, 39, 69, 71, 84]
  | 3 => [9, 20, 41, 49, 61, 78, 82]
  | 4 => [2, 41, 59, 83, 85, 87, 89]
  | _ => [40, 49, 60, 77, 85, 90]
theorem rightSignature_index1 : ∀ d : Fin 6, ∀ row : List State, rightSignature (samples1 d) (literalDomain.zip row) = indexSignature (rightIndices1 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (-2,5), patchState (literalDomain.zip row) (0,-4), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (3,-4), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,0)] = encode [(row[12]?).getD (0,0), (row[29]?).getD (0,0), (row[41]?).getD (0,0), (row[59]?).getD (0,0), (row[71]?).getD (0,0), (row[85]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup12 row, indexedLookup29 row, indexedLookup41 row, indexedLookup59 row, indexedLookup71 row, indexedLookup85 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,1), patchState (literalDomain.zip row) (-5,3), patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (4,-4), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,-2)] = encode [(row[1]?).getD (0,0), (row[3]?).getD (0,0), (row[39]?).getD (0,0), (row[79]?).getD (0,0), (row[84]?).getD (0,0), (row[88]?).getD (0,0)]
    rw [indexedLookup1 row, indexedLookup3 row, indexedLookup39 row, indexedLookup79 row, indexedLookup84 row, indexedLookup88 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,2), patchState (literalDomain.zip row) (-3,-2), patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (3,-4), patchState (literalDomain.zip row) (4,1)] = encode [(row[9]?).getD (0,0), (row[13]?).getD (0,0), (row[30]?).getD (0,0), (row[39]?).getD (0,0), (row[69]?).getD (0,0), (row[71]?).getD (0,0), (row[84]?).getD (0,0)]
    rw [indexedLookup9 row, indexedLookup13 row, indexedLookup30 row, indexedLookup39 row, indexedLookup69 row, indexedLookup71 row, indexedLookup84 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,2), patchState (literalDomain.zip row) (-3,5), patchState (literalDomain.zip row) (0,-4), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (2,-5), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (4,-1)] = encode [(row[9]?).getD (0,0), (row[20]?).getD (0,0), (row[41]?).getD (0,0), (row[49]?).getD (0,0), (row[61]?).getD (0,0), (row[78]?).getD (0,0), (row[82]?).getD (0,0)]
    rw [indexedLookup9 row, indexedLookup20 row, indexedLookup41 row, indexedLookup49 row, indexedLookup61 row, indexedLookup78 row, indexedLookup82 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,2), patchState (literalDomain.zip row) (0,-4), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (4,0), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,-3), patchState (literalDomain.zip row) (5,-1)] = encode [(row[2]?).getD (0,0), (row[41]?).getD (0,0), (row[59]?).getD (0,0), (row[83]?).getD (0,0), (row[85]?).getD (0,0), (row[87]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup2 row, indexedLookup41 row, indexedLookup59 row, indexedLookup83 row, indexedLookup85 row, indexedLookup87 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (3,2), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,0)] = encode [(row[40]?).getD (0,0), (row[49]?).getD (0,0), (row[60]?).getD (0,0), (row[77]?).getD (0,0), (row[85]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup40 row, indexedLookup49 row, indexedLookup60 row, indexedLookup77 row, indexedLookup85 row, indexedLookup90 row]
def leftIndices2 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [12, 21, 37, 38, 39, 52, 59, 70, 80, 83]
  | 1 => [1, 4, 59, 61, 78, 87]
  | 2 => [6, 30, 38, 77, 79, 89]
  | 3 => [10, 39, 51, 67, 73, 78]
  | 4 => [4, 31, 37, 86, 88, 89]
  | _ => [21, 27, 60, 71, 81, 84]
theorem leftSignature_index2 : ∀ d : Fin 6, ∀ row : List State, leftSignature (direction d) (samples2 d) (literalDomain.zip row) = indexSignature (leftIndices2 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (-2,-3), patchState (literalDomain.zip row) (-1,3), patchState (literalDomain.zip row) (-1,4), patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (1,-4), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (4,-3), patchState (literalDomain.zip row) (4,0)] = encode [(row[12]?).getD (0,0), (row[21]?).getD (0,0), (row[37]?).getD (0,0), (row[38]?).getD (0,0), (row[39]?).getD (0,0), (row[52]?).getD (0,0), (row[59]?).getD (0,0), (row[70]?).getD (0,0), (row[80]?).getD (0,0), (row[83]?).getD (0,0)]
    rw [indexedLookup12 row, indexedLookup21 row, indexedLookup37 row, indexedLookup38 row, indexedLookup39 row, indexedLookup52 row, indexedLookup59 row, indexedLookup70 row, indexedLookup80 row, indexedLookup83 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,1), patchState (literalDomain.zip row) (-5,4), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (2,-5), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (5,-3)] = encode [(row[1]?).getD (0,0), (row[4]?).getD (0,0), (row[59]?).getD (0,0), (row[61]?).getD (0,0), (row[78]?).getD (0,0), (row[87]?).getD (0,0)]
    rw [indexedLookup1 row, indexedLookup4 row, indexedLookup59 row, indexedLookup61 row, indexedLookup78 row, indexedLookup87 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,-1), patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (-1,4), patchState (literalDomain.zip row) (3,2), patchState (literalDomain.zip row) (4,-4), patchState (literalDomain.zip row) (5,-1)] = encode [(row[6]?).getD (0,0), (row[30]?).getD (0,0), (row[38]?).getD (0,0), (row[77]?).getD (0,0), (row[79]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup6 row, indexedLookup30 row, indexedLookup38 row, indexedLookup77 row, indexedLookup79 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,3), patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (1,-5), patchState (literalDomain.zip row) (2,1), patchState (literalDomain.zip row) (3,-2), patchState (literalDomain.zip row) (4,-5)] = encode [(row[10]?).getD (0,0), (row[39]?).getD (0,0), (row[51]?).getD (0,0), (row[67]?).getD (0,0), (row[73]?).getD (0,0), (row[78]?).getD (0,0)]
    rw [indexedLookup10 row, indexedLookup39 row, indexedLookup51 row, indexedLookup67 row, indexedLookup73 row, indexedLookup78 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,4), patchState (literalDomain.zip row) (-1,-3), patchState (literalDomain.zip row) (-1,3), patchState (literalDomain.zip row) (5,-4), patchState (literalDomain.zip row) (5,-2), patchState (literalDomain.zip row) (5,-1)] = encode [(row[4]?).getD (0,0), (row[31]?).getD (0,0), (row[37]?).getD (0,0), (row[86]?).getD (0,0), (row[88]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup4 row, indexedLookup31 row, indexedLookup37 row, indexedLookup86 row, indexedLookup88 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,-3), patchState (literalDomain.zip row) (-2,3), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (3,-4), patchState (literalDomain.zip row) (4,-2), patchState (literalDomain.zip row) (4,1)] = encode [(row[21]?).getD (0,0), (row[27]?).getD (0,0), (row[60]?).getD (0,0), (row[71]?).getD (0,0), (row[81]?).getD (0,0), (row[84]?).getD (0,0)]
    rw [indexedLookup21 row, indexedLookup27 row, indexedLookup60 row, indexedLookup71 row, indexedLookup81 row, indexedLookup84 row]
def rightIndices2 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [20, 31, 48, 49, 50, 62, 69, 78, 87, 90]
  | 1 => [2, 5, 60, 62, 79, 88]
  | 2 => [0, 21, 29, 69, 72, 83]
  | 3 => [3, 29, 40, 57, 64, 70]
  | 4 => [3, 30, 36, 85, 87, 88]
  | _ => [30, 36, 69, 78, 87, 90]
theorem rightSignature_index2 : ∀ d : Fin 6, ∀ row : List State, rightSignature (samples2 d) (literalDomain.zip row) = indexSignature (rightIndices2 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,5), patchState (literalDomain.zip row) (-1,-3), patchState (literalDomain.zip row) (0,3), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (2,-4), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (5,-3), patchState (literalDomain.zip row) (5,0)] = encode [(row[20]?).getD (0,0), (row[31]?).getD (0,0), (row[48]?).getD (0,0), (row[49]?).getD (0,0), (row[50]?).getD (0,0), (row[62]?).getD (0,0), (row[69]?).getD (0,0), (row[78]?).getD (0,0), (row[87]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup20 row, indexedLookup31 row, indexedLookup48 row, indexedLookup49 row, indexedLookup50 row, indexedLookup62 row, indexedLookup69 row, indexedLookup78 row, indexedLookup87 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,2), patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (2,-4), patchState (literalDomain.zip row) (4,-4), patchState (literalDomain.zip row) (5,-2)] = encode [(row[2]?).getD (0,0), (row[5]?).getD (0,0), (row[60]?).getD (0,0), (row[62]?).getD (0,0), (row[79]?).getD (0,0), (row[88]?).getD (0,0)]
    rw [indexedLookup2 row, indexedLookup5 row, indexedLookup60 row, indexedLookup62 row, indexedLookup79 row, indexedLookup88 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,0), patchState (literalDomain.zip row) (-2,-3), patchState (literalDomain.zip row) (-2,5), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (3,-3), patchState (literalDomain.zip row) (4,0)] = encode [(row[0]?).getD (0,0), (row[21]?).getD (0,0), (row[29]?).getD (0,0), (row[69]?).getD (0,0), (row[72]?).getD (0,0), (row[83]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup21 row, indexedLookup29 row, indexedLookup69 row, indexedLookup72 row, indexedLookup83 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,3), patchState (literalDomain.zip row) (-2,5), patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (1,1), patchState (literalDomain.zip row) (2,-2), patchState (literalDomain.zip row) (3,-5)] = encode [(row[3]?).getD (0,0), (row[29]?).getD (0,0), (row[40]?).getD (0,0), (row[57]?).getD (0,0), (row[64]?).getD (0,0), (row[70]?).getD (0,0)]
    rw [indexedLookup3 row, indexedLookup29 row, indexedLookup40 row, indexedLookup57 row, indexedLookup64 row, indexedLookup70 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,3), patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (-1,2), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,-3), patchState (literalDomain.zip row) (5,-2)] = encode [(row[3]?).getD (0,0), (row[30]?).getD (0,0), (row[36]?).getD (0,0), (row[85]?).getD (0,0), (row[87]?).getD (0,0), (row[88]?).getD (0,0)]
    rw [indexedLookup3 row, indexedLookup30 row, indexedLookup36 row, indexedLookup85 row, indexedLookup87 row, indexedLookup88 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (-1,2), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (5,-3), patchState (literalDomain.zip row) (5,0)] = encode [(row[30]?).getD (0,0), (row[36]?).getD (0,0), (row[69]?).getD (0,0), (row[78]?).getD (0,0), (row[87]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup30 row, indexedLookup36 row, indexedLookup69 row, indexedLookup78 row, indexedLookup87 row, indexedLookup90 row]
def leftIndices3 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [5, 13, 27, 28, 41, 49, 61, 76, 78, 81]
  | 1 => [0, 11, 53, 58, 70, 76, 87]
  | 2 => [13, 17, 40, 49, 84, 86, 88]
  | 3 => [11, 50, 51, 69, 81, 84, 85, 90]
  | 4 => [5, 22, 28, 53, 59, 87, 90]
  | _ => [13, 19, 50, 62, 80, 84]
theorem leftSignature_index3 : ∀ d : Fin 6, ∀ row : List State, leftSignature (direction d) (samples3 d) (literalDomain.zip row) = indexSignature (leftIndices3 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (-3,-2), patchState (literalDomain.zip row) (-2,3), patchState (literalDomain.zip row) (-2,4), patchState (literalDomain.zip row) (0,-4), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (2,-5), patchState (literalDomain.zip row) (3,1), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (4,-2)] = encode [(row[5]?).getD (0,0), (row[13]?).getD (0,0), (row[27]?).getD (0,0), (row[28]?).getD (0,0), (row[41]?).getD (0,0), (row[49]?).getD (0,0), (row[61]?).getD (0,0), (row[76]?).getD (0,0), (row[78]?).getD (0,0), (row[81]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup13 row, indexedLookup27 row, indexedLookup28 row, indexedLookup41 row, indexedLookup49 row, indexedLookup61 row, indexedLookup76 row, indexedLookup78 row, indexedLookup81 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,0), patchState (literalDomain.zip row) (-4,4), patchState (literalDomain.zip row) (1,-3), patchState (literalDomain.zip row) (1,2), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (3,1), patchState (literalDomain.zip row) (5,-3)] = encode [(row[0]?).getD (0,0), (row[11]?).getD (0,0), (row[53]?).getD (0,0), (row[58]?).getD (0,0), (row[70]?).getD (0,0), (row[76]?).getD (0,0), (row[87]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup11 row, indexedLookup53 row, indexedLookup58 row, indexedLookup70 row, indexedLookup76 row, indexedLookup87 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,-2), patchState (literalDomain.zip row) (-3,2), patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,-4), patchState (literalDomain.zip row) (5,-2)] = encode [(row[13]?).getD (0,0), (row[17]?).getD (0,0), (row[40]?).getD (0,0), (row[49]?).getD (0,0), (row[84]?).getD (0,0), (row[86]?).getD (0,0), (row[88]?).getD (0,0)]
    rw [indexedLookup13 row, indexedLookup17 row, indexedLookup40 row, indexedLookup49 row, indexedLookup84 row, indexedLookup86 row, indexedLookup88 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,4), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (1,-5), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (4,-2), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,0)] = encode [(row[11]?).getD (0,0), (row[50]?).getD (0,0), (row[51]?).getD (0,0), (row[69]?).getD (0,0), (row[81]?).getD (0,0), (row[84]?).getD (0,0), (row[85]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup11 row, indexedLookup50 row, indexedLookup51 row, indexedLookup69 row, indexedLookup81 row, indexedLookup84 row, indexedLookup85 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (-2,-2), patchState (literalDomain.zip row) (-2,4), patchState (literalDomain.zip row) (1,-3), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (5,-3), patchState (literalDomain.zip row) (5,0)] = encode [(row[5]?).getD (0,0), (row[22]?).getD (0,0), (row[28]?).getD (0,0), (row[53]?).getD (0,0), (row[59]?).getD (0,0), (row[87]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup22 row, indexedLookup28 row, indexedLookup53 row, indexedLookup59 row, indexedLookup87 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,-2), patchState (literalDomain.zip row) (-3,4), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (2,-4), patchState (literalDomain.zip row) (4,-3), patchState (literalDomain.zip row) (4,1)] = encode [(row[13]?).getD (0,0), (row[19]?).getD (0,0), (row[50]?).getD (0,0), (row[62]?).getD (0,0), (row[80]?).getD (0,0), (row[84]?).getD (0,0)]
    rw [indexedLookup13 row, indexedLookup19 row, indexedLookup50 row, indexedLookup62 row, indexedLookup80 row, indexedLookup84 row]
def rightIndices3 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [12, 22, 37, 38, 52, 60, 70, 84, 85, 88]
  | 1 => [1, 12, 54, 59, 71, 77, 88]
  | 2 => [6, 10, 30, 39, 77, 80, 82]
  | 3 => [4, 39, 40, 59, 73, 76, 78, 83]
  | 4 => [4, 21, 27, 52, 58, 86, 89]
  | _ => [21, 27, 60, 70, 86, 90]
theorem rightSignature_index3 : ∀ d : Fin 6, ∀ row : List State, rightSignature (samples3 d) (literalDomain.zip row) = indexSignature (rightIndices3 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (-2,-2), patchState (literalDomain.zip row) (-1,3), patchState (literalDomain.zip row) (-1,4), patchState (literalDomain.zip row) (1,-4), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,-2)] = encode [(row[12]?).getD (0,0), (row[22]?).getD (0,0), (row[37]?).getD (0,0), (row[38]?).getD (0,0), (row[52]?).getD (0,0), (row[60]?).getD (0,0), (row[70]?).getD (0,0), (row[84]?).getD (0,0), (row[85]?).getD (0,0), (row[88]?).getD (0,0)]
    rw [indexedLookup12 row, indexedLookup22 row, indexedLookup37 row, indexedLookup38 row, indexedLookup52 row, indexedLookup60 row, indexedLookup70 row, indexedLookup84 row, indexedLookup85 row, indexedLookup88 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,1), patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (1,-2), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (3,-4), patchState (literalDomain.zip row) (3,2), patchState (literalDomain.zip row) (5,-2)] = encode [(row[1]?).getD (0,0), (row[12]?).getD (0,0), (row[54]?).getD (0,0), (row[59]?).getD (0,0), (row[71]?).getD (0,0), (row[77]?).getD (0,0), (row[88]?).getD (0,0)]
    rw [indexedLookup1 row, indexedLookup12 row, indexedLookup54 row, indexedLookup59 row, indexedLookup71 row, indexedLookup77 row, indexedLookup88 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,-1), patchState (literalDomain.zip row) (-4,3), patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (3,2), patchState (literalDomain.zip row) (4,-3), patchState (literalDomain.zip row) (4,-1)] = encode [(row[6]?).getD (0,0), (row[10]?).getD (0,0), (row[30]?).getD (0,0), (row[39]?).getD (0,0), (row[77]?).getD (0,0), (row[80]?).getD (0,0), (row[82]?).getD (0,0)]
    rw [indexedLookup6 row, indexedLookup10 row, indexedLookup30 row, indexedLookup39 row, indexedLookup77 row, indexedLookup80 row, indexedLookup82 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,4), patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (3,-2), patchState (literalDomain.zip row) (3,1), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (4,0)] = encode [(row[4]?).getD (0,0), (row[39]?).getD (0,0), (row[40]?).getD (0,0), (row[59]?).getD (0,0), (row[73]?).getD (0,0), (row[76]?).getD (0,0), (row[78]?).getD (0,0), (row[83]?).getD (0,0)]
    rw [indexedLookup4 row, indexedLookup39 row, indexedLookup40 row, indexedLookup59 row, indexedLookup73 row, indexedLookup76 row, indexedLookup78 row, indexedLookup83 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,4), patchState (literalDomain.zip row) (-2,-3), patchState (literalDomain.zip row) (-2,3), patchState (literalDomain.zip row) (1,-4), patchState (literalDomain.zip row) (1,2), patchState (literalDomain.zip row) (5,-4), patchState (literalDomain.zip row) (5,-1)] = encode [(row[4]?).getD (0,0), (row[21]?).getD (0,0), (row[27]?).getD (0,0), (row[52]?).getD (0,0), (row[58]?).getD (0,0), (row[86]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup4 row, indexedLookup21 row, indexedLookup27 row, indexedLookup52 row, indexedLookup58 row, indexedLookup86 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,-3), patchState (literalDomain.zip row) (-2,3), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (5,-4), patchState (literalDomain.zip row) (5,0)] = encode [(row[21]?).getD (0,0), (row[27]?).getD (0,0), (row[60]?).getD (0,0), (row[70]?).getD (0,0), (row[86]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup21 row, indexedLookup27 row, indexedLookup60 row, indexedLookup70 row, indexedLookup86 row, indexedLookup90 row]
def leftIndices4 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [5, 6, 28, 39, 40, 61, 68, 79]
  | 1 => [6, 11, 59, 70, 85, 89]
  | 2 => [19, 21, 51, 69, 88, 89, 90]
  | 3 => [19, 20, 22, 50, 63, 69, 70, 86]
  | 4 => [5, 14, 28, 43, 60, 88, 90]
  | _ => [0, 19, 52, 80]
theorem leftSignature_index4 : ∀ d : Fin 6, ∀ row : List State, leftSignature (direction d) (samples4 d) (literalDomain.zip row) = indexSignature (leftIndices4 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (-4,-1), patchState (literalDomain.zip row) (-2,4), patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (2,-5), patchState (literalDomain.zip row) (2,2), patchState (literalDomain.zip row) (4,-4)] = encode [(row[5]?).getD (0,0), (row[6]?).getD (0,0), (row[28]?).getD (0,0), (row[39]?).getD (0,0), (row[40]?).getD (0,0), (row[61]?).getD (0,0), (row[68]?).getD (0,0), (row[79]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup6 row, indexedLookup28 row, indexedLookup39 row, indexedLookup40 row, indexedLookup61 row, indexedLookup68 row, indexedLookup79 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,-1), patchState (literalDomain.zip row) (-4,4), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,-1)] = encode [(row[6]?).getD (0,0), (row[11]?).getD (0,0), (row[59]?).getD (0,0), (row[70]?).getD (0,0), (row[85]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup6 row, indexedLookup11 row, indexedLookup59 row, indexedLookup70 row, indexedLookup85 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,4), patchState (literalDomain.zip row) (-2,-3), patchState (literalDomain.zip row) (1,-5), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (5,-2), patchState (literalDomain.zip row) (5,-1), patchState (literalDomain.zip row) (5,0)] = encode [(row[19]?).getD (0,0), (row[21]?).getD (0,0), (row[51]?).getD (0,0), (row[69]?).getD (0,0), (row[88]?).getD (0,0), (row[89]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup19 row, indexedLookup21 row, indexedLookup51 row, indexedLookup69 row, indexedLookup88 row, indexedLookup89 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,4), patchState (literalDomain.zip row) (-3,5), patchState (literalDomain.zip row) (-2,-2), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (2,-3), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (5,-4)] = encode [(row[19]?).getD (0,0), (row[20]?).getD (0,0), (row[22]?).getD (0,0), (row[50]?).getD (0,0), (row[63]?).getD (0,0), (row[69]?).getD (0,0), (row[70]?).getD (0,0), (row[86]?).getD (0,0)]
    rw [indexedLookup19 row, indexedLookup20 row, indexedLookup22 row, indexedLookup50 row, indexedLookup63 row, indexedLookup69 row, indexedLookup70 row, indexedLookup86 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (-3,-1), patchState (literalDomain.zip row) (-2,4), patchState (literalDomain.zip row) (0,-2), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (5,-2), patchState (literalDomain.zip row) (5,0)] = encode [(row[5]?).getD (0,0), (row[14]?).getD (0,0), (row[28]?).getD (0,0), (row[43]?).getD (0,0), (row[60]?).getD (0,0), (row[88]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup14 row, indexedLookup28 row, indexedLookup43 row, indexedLookup60 row, indexedLookup88 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,0), patchState (literalDomain.zip row) (-3,4), patchState (literalDomain.zip row) (1,-4), patchState (literalDomain.zip row) (4,-3)] = encode [(row[0]?).getD (0,0), (row[19]?).getD (0,0), (row[52]?).getD (0,0), (row[80]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup19 row, indexedLookup52 row, indexedLookup80 row]
def rightIndices4 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [12, 14, 38, 50, 51, 70, 77, 86]
  | 1 => [7, 12, 60, 71, 86, 90]
  | 2 => [12, 13, 41, 60, 82, 83, 84]
  | 3 => [11, 12, 13, 39, 53, 59, 61, 79]
  | 4 => [4, 13, 27, 42, 59, 87, 89]
  | _ => [6, 27, 61, 86]
theorem rightSignature_index4 : ∀ d : Fin 6, ∀ row : List State, rightSignature (samples4 d) (literalDomain.zip row) = indexSignature (rightIndices4 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (-3,-1), patchState (literalDomain.zip row) (-1,4), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (1,-5), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (3,2), patchState (literalDomain.zip row) (5,-4)] = encode [(row[12]?).getD (0,0), (row[14]?).getD (0,0), (row[38]?).getD (0,0), (row[50]?).getD (0,0), (row[51]?).getD (0,0), (row[70]?).getD (0,0), (row[77]?).getD (0,0), (row[86]?).getD (0,0)]
    rw [indexedLookup12 row, indexedLookup14 row, indexedLookup38 row, indexedLookup50 row, indexedLookup51 row, indexedLookup70 row, indexedLookup77 row, indexedLookup86 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,0), patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (3,-4), patchState (literalDomain.zip row) (5,-4), patchState (literalDomain.zip row) (5,0)] = encode [(row[7]?).getD (0,0), (row[12]?).getD (0,0), (row[60]?).getD (0,0), (row[71]?).getD (0,0), (row[86]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup7 row, indexedLookup12 row, indexedLookup60 row, indexedLookup71 row, indexedLookup86 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (-3,-2), patchState (literalDomain.zip row) (0,-4), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (4,-1), patchState (literalDomain.zip row) (4,0), patchState (literalDomain.zip row) (4,1)] = encode [(row[12]?).getD (0,0), (row[13]?).getD (0,0), (row[41]?).getD (0,0), (row[60]?).getD (0,0), (row[82]?).getD (0,0), (row[83]?).getD (0,0), (row[84]?).getD (0,0)]
    rw [indexedLookup12 row, indexedLookup13 row, indexedLookup41 row, indexedLookup60 row, indexedLookup82 row, indexedLookup83 row, indexedLookup84 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,4), patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (-3,-2), patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (1,-3), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (2,-5), patchState (literalDomain.zip row) (4,-4)] = encode [(row[11]?).getD (0,0), (row[12]?).getD (0,0), (row[13]?).getD (0,0), (row[39]?).getD (0,0), (row[53]?).getD (0,0), (row[59]?).getD (0,0), (row[61]?).getD (0,0), (row[79]?).getD (0,0)]
    rw [indexedLookup11 row, indexedLookup12 row, indexedLookup13 row, indexedLookup39 row, indexedLookup53 row, indexedLookup59 row, indexedLookup61 row, indexedLookup79 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,4), patchState (literalDomain.zip row) (-3,-2), patchState (literalDomain.zip row) (-2,3), patchState (literalDomain.zip row) (0,-3), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (5,-3), patchState (literalDomain.zip row) (5,-1)] = encode [(row[4]?).getD (0,0), (row[13]?).getD (0,0), (row[27]?).getD (0,0), (row[42]?).getD (0,0), (row[59]?).getD (0,0), (row[87]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup4 row, indexedLookup13 row, indexedLookup27 row, indexedLookup42 row, indexedLookup59 row, indexedLookup87 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,-1), patchState (literalDomain.zip row) (-2,3), patchState (literalDomain.zip row) (2,-5), patchState (literalDomain.zip row) (5,-4)] = encode [(row[6]?).getD (0,0), (row[27]?).getD (0,0), (row[61]?).getD (0,0), (row[86]?).getD (0,0)]
    rw [indexedLookup6 row, indexedLookup27 row, indexedLookup61 row, indexedLookup86 row]
def leftIndices5 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [5, 6, 7, 8, 40, 49, 68, 71, 78, 81]
  | 1 => [0, 51, 68, 85, 87, 89]
  | 2 => [28, 40, 60, 84, 86, 90]
  | 3 => [12, 38, 51, 69, 84, 85]
  | 4 => [17, 20, 50, 58, 88, 90]
  | _ => [9, 12, 50, 81]
theorem leftSignature_index5 : ∀ d : Fin 6, ∀ row : List State, leftSignature (direction d) (samples5 d) (literalDomain.zip row) = indexSignature (leftIndices5 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (-4,-1), patchState (literalDomain.zip row) (-4,0), patchState (literalDomain.zip row) (-4,1), patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (2,2), patchState (literalDomain.zip row) (3,-4), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (4,-2)] = encode [(row[5]?).getD (0,0), (row[6]?).getD (0,0), (row[7]?).getD (0,0), (row[8]?).getD (0,0), (row[40]?).getD (0,0), (row[49]?).getD (0,0), (row[68]?).getD (0,0), (row[71]?).getD (0,0), (row[78]?).getD (0,0), (row[81]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup6 row, indexedLookup7 row, indexedLookup8 row, indexedLookup40 row, indexedLookup49 row, indexedLookup68 row, indexedLookup71 row, indexedLookup78 row, indexedLookup81 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,0), patchState (literalDomain.zip row) (1,-5), patchState (literalDomain.zip row) (2,2), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,-3), patchState (literalDomain.zip row) (5,-1)] = encode [(row[0]?).getD (0,0), (row[51]?).getD (0,0), (row[68]?).getD (0,0), (row[85]?).getD (0,0), (row[87]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup51 row, indexedLookup68 row, indexedLookup85 row, indexedLookup87 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,4), patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,-4), patchState (literalDomain.zip row) (5,0)] = encode [(row[28]?).getD (0,0), (row[40]?).getD (0,0), (row[60]?).getD (0,0), (row[84]?).getD (0,0), (row[86]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup28 row, indexedLookup40 row, indexedLookup60 row, indexedLookup84 row, indexedLookup86 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (-1,4), patchState (literalDomain.zip row) (1,-5), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,-5)] = encode [(row[12]?).getD (0,0), (row[38]?).getD (0,0), (row[51]?).getD (0,0), (row[69]?).getD (0,0), (row[84]?).getD (0,0), (row[85]?).getD (0,0)]
    rw [indexedLookup12 row, indexedLookup38 row, indexedLookup51 row, indexedLookup69 row, indexedLookup84 row, indexedLookup85 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,2), patchState (literalDomain.zip row) (-3,5), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (1,2), patchState (literalDomain.zip row) (5,-2), patchState (literalDomain.zip row) (5,0)] = encode [(row[17]?).getD (0,0), (row[20]?).getD (0,0), (row[50]?).getD (0,0), (row[58]?).getD (0,0), (row[88]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup17 row, indexedLookup20 row, indexedLookup50 row, indexedLookup58 row, indexedLookup88 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,2), patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (4,-2)] = encode [(row[9]?).getD (0,0), (row[12]?).getD (0,0), (row[50]?).getD (0,0), (row[81]?).getD (0,0)]
    rw [indexedLookup9 row, indexedLookup12 row, indexedLookup50 row, indexedLookup81 row]
def rightIndices5 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [12, 14, 15, 16, 51, 60, 77, 79, 85, 88]
  | 1 => [1, 52, 69, 86, 88, 90]
  | 2 => [20, 30, 50, 77, 80, 84]
  | 3 => [5, 28, 40, 59, 76, 78]
  | 4 => [16, 19, 49, 57, 87, 89]
  | _ => [16, 19, 60, 87]
theorem rightSignature_index5 : ∀ d : Fin 6, ∀ row : List State, rightSignature (samples5 d) (literalDomain.zip row) = indexSignature (rightIndices5 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (-3,-1), patchState (literalDomain.zip row) (-3,0), patchState (literalDomain.zip row) (-3,1), patchState (literalDomain.zip row) (1,-5), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (3,2), patchState (literalDomain.zip row) (4,-4), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,-2)] = encode [(row[12]?).getD (0,0), (row[14]?).getD (0,0), (row[15]?).getD (0,0), (row[16]?).getD (0,0), (row[51]?).getD (0,0), (row[60]?).getD (0,0), (row[77]?).getD (0,0), (row[79]?).getD (0,0), (row[85]?).getD (0,0), (row[88]?).getD (0,0)]
    rw [indexedLookup12 row, indexedLookup14 row, indexedLookup15 row, indexedLookup16 row, indexedLookup51 row, indexedLookup60 row, indexedLookup77 row, indexedLookup79 row, indexedLookup85 row, indexedLookup88 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,1), patchState (literalDomain.zip row) (1,-4), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (5,-4), patchState (literalDomain.zip row) (5,-2), patchState (literalDomain.zip row) (5,0)] = encode [(row[1]?).getD (0,0), (row[52]?).getD (0,0), (row[69]?).getD (0,0), (row[86]?).getD (0,0), (row[88]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup1 row, indexedLookup52 row, indexedLookup69 row, indexedLookup86 row, indexedLookup88 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,5), patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (3,2), patchState (literalDomain.zip row) (4,-3), patchState (literalDomain.zip row) (4,1)] = encode [(row[20]?).getD (0,0), (row[30]?).getD (0,0), (row[50]?).getD (0,0), (row[77]?).getD (0,0), (row[80]?).getD (0,0), (row[84]?).getD (0,0)]
    rw [indexedLookup20 row, indexedLookup30 row, indexedLookup50 row, indexedLookup77 row, indexedLookup80 row, indexedLookup84 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (-2,4), patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (3,1), patchState (literalDomain.zip row) (4,-5)] = encode [(row[5]?).getD (0,0), (row[28]?).getD (0,0), (row[40]?).getD (0,0), (row[59]?).getD (0,0), (row[76]?).getD (0,0), (row[78]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup28 row, indexedLookup40 row, indexedLookup59 row, indexedLookup76 row, indexedLookup78 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,1), patchState (literalDomain.zip row) (-3,4), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (1,1), patchState (literalDomain.zip row) (5,-3), patchState (literalDomain.zip row) (5,-1)] = encode [(row[16]?).getD (0,0), (row[19]?).getD (0,0), (row[49]?).getD (0,0), (row[57]?).getD (0,0), (row[87]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup16 row, indexedLookup19 row, indexedLookup49 row, indexedLookup57 row, indexedLookup87 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-3,1), patchState (literalDomain.zip row) (-3,4), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (5,-3)] = encode [(row[16]?).getD (0,0), (row[19]?).getD (0,0), (row[60]?).getD (0,0), (row[87]?).getD (0,0)]
    rw [indexedLookup16 row, indexedLookup19 row, indexedLookup60 row, indexedLookup87 row]
def leftIndices6 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [0, 1, 2, 3, 4, 5, 6, 13, 21, 30, 40, 83]
  | 1 => [21, 40, 51, 61, 70, 78, 83, 85, 87]
  | 2 => [66, 69, 70, 85, 86, 87, 88, 89, 90]
  | 3 => [39, 50, 60, 69, 77, 78, 84, 88, 90]
  | 4 => [5, 12, 20, 29, 39, 50, 52, 90]
  | _ => [3, 50, 83]
theorem leftSignature_index6 : ∀ d : Fin 6, ∀ row : List State, leftSignature (direction d) (samples6 d) (literalDomain.zip row) = indexSignature (leftIndices6 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,0), patchState (literalDomain.zip row) (-5,1), patchState (literalDomain.zip row) (-5,2), patchState (literalDomain.zip row) (-5,3), patchState (literalDomain.zip row) (-5,4), patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (-4,-1), patchState (literalDomain.zip row) (-3,-2), patchState (literalDomain.zip row) (-2,-3), patchState (literalDomain.zip row) (-1,-4), patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (4,0)] = encode [(row[0]?).getD (0,0), (row[1]?).getD (0,0), (row[2]?).getD (0,0), (row[3]?).getD (0,0), (row[4]?).getD (0,0), (row[5]?).getD (0,0), (row[6]?).getD (0,0), (row[13]?).getD (0,0), (row[21]?).getD (0,0), (row[30]?).getD (0,0), (row[40]?).getD (0,0), (row[83]?).getD (0,0)]
    rw [indexedLookup0 row, indexedLookup1 row, indexedLookup2 row, indexedLookup3 row, indexedLookup4 row, indexedLookup5 row, indexedLookup6 row, indexedLookup13 row, indexedLookup21 row, indexedLookup30 row, indexedLookup40 row, indexedLookup83 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,-3), patchState (literalDomain.zip row) (0,-5), patchState (literalDomain.zip row) (1,-5), patchState (literalDomain.zip row) (2,-5), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (4,0), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,-3)] = encode [(row[21]?).getD (0,0), (row[40]?).getD (0,0), (row[51]?).getD (0,0), (row[61]?).getD (0,0), (row[70]?).getD (0,0), (row[78]?).getD (0,0), (row[83]?).getD (0,0), (row[85]?).getD (0,0), (row[87]?).getD (0,0)]
    rw [indexedLookup21 row, indexedLookup40 row, indexedLookup51 row, indexedLookup61 row, indexedLookup70 row, indexedLookup78 row, indexedLookup83 row, indexedLookup85 row, indexedLookup87 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (2,0), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (5,-5), patchState (literalDomain.zip row) (5,-4), patchState (literalDomain.zip row) (5,-3), patchState (literalDomain.zip row) (5,-2), patchState (literalDomain.zip row) (5,-1), patchState (literalDomain.zip row) (5,0)] = encode [(row[66]?).getD (0,0), (row[69]?).getD (0,0), (row[70]?).getD (0,0), (row[85]?).getD (0,0), (row[86]?).getD (0,0), (row[87]?).getD (0,0), (row[88]?).getD (0,0), (row[89]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup66 row, indexedLookup69 row, indexedLookup70 row, indexedLookup85 row, indexedLookup86 row, indexedLookup87 row, indexedLookup88 row, indexedLookup89 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (2,3), patchState (literalDomain.zip row) (3,2), patchState (literalDomain.zip row) (4,-5), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,-2), patchState (literalDomain.zip row) (5,0)] = encode [(row[39]?).getD (0,0), (row[50]?).getD (0,0), (row[60]?).getD (0,0), (row[69]?).getD (0,0), (row[77]?).getD (0,0), (row[78]?).getD (0,0), (row[84]?).getD (0,0), (row[88]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup39 row, indexedLookup50 row, indexedLookup60 row, indexedLookup69 row, indexedLookup77 row, indexedLookup78 row, indexedLookup84 row, indexedLookup88 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,5), patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (-3,5), patchState (literalDomain.zip row) (-2,5), patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (1,-4), patchState (literalDomain.zip row) (5,0)] = encode [(row[5]?).getD (0,0), (row[12]?).getD (0,0), (row[20]?).getD (0,0), (row[29]?).getD (0,0), (row[39]?).getD (0,0), (row[50]?).getD (0,0), (row[52]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup5 row, indexedLookup12 row, indexedLookup20 row, indexedLookup29 row, indexedLookup39 row, indexedLookup50 row, indexedLookup52 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,3), patchState (literalDomain.zip row) (0,5), patchState (literalDomain.zip row) (4,0)] = encode [(row[3]?).getD (0,0), (row[50]?).getD (0,0), (row[83]?).getD (0,0)]
    rw [indexedLookup3 row, indexedLookup50 row, indexedLookup83 row]
def rightIndices6 (d : Fin 6) : List Nat :=
  match d.val with
  | 0 => [7, 8, 9, 10, 11, 12, 14, 22, 31, 41, 51, 90]
  | 1 => [22, 41, 52, 62, 71, 79, 84, 86, 88]
  | 2 => [57, 60, 62, 79, 80, 81, 82, 83, 84]
  | 3 => [29, 39, 49, 59, 68, 70, 76, 81, 83]
  | 4 => [4, 11, 19, 28, 38, 49, 51, 89]
  | _ => [9, 60, 89]
theorem rightSignature_index6 : ∀ d : Fin 6, ∀ row : List State, rightSignature (samples6 d) (literalDomain.zip row) = indexSignature (rightIndices6 d) row := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))))
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,0), patchState (literalDomain.zip row) (-4,1), patchState (literalDomain.zip row) (-4,2), patchState (literalDomain.zip row) (-4,3), patchState (literalDomain.zip row) (-4,4), patchState (literalDomain.zip row) (-4,5), patchState (literalDomain.zip row) (-3,-1), patchState (literalDomain.zip row) (-2,-2), patchState (literalDomain.zip row) (-1,-3), patchState (literalDomain.zip row) (0,-4), patchState (literalDomain.zip row) (1,-5), patchState (literalDomain.zip row) (5,0)] = encode [(row[7]?).getD (0,0), (row[8]?).getD (0,0), (row[9]?).getD (0,0), (row[10]?).getD (0,0), (row[11]?).getD (0,0), (row[12]?).getD (0,0), (row[14]?).getD (0,0), (row[22]?).getD (0,0), (row[31]?).getD (0,0), (row[41]?).getD (0,0), (row[51]?).getD (0,0), (row[90]?).getD (0,0)]
    rw [indexedLookup7 row, indexedLookup8 row, indexedLookup9 row, indexedLookup10 row, indexedLookup11 row, indexedLookup12 row, indexedLookup14 row, indexedLookup22 row, indexedLookup31 row, indexedLookup41 row, indexedLookup51 row, indexedLookup90 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,-2), patchState (literalDomain.zip row) (0,-4), patchState (literalDomain.zip row) (1,-4), patchState (literalDomain.zip row) (2,-4), patchState (literalDomain.zip row) (3,-4), patchState (literalDomain.zip row) (4,-4), patchState (literalDomain.zip row) (4,1), patchState (literalDomain.zip row) (5,-4), patchState (literalDomain.zip row) (5,-2)] = encode [(row[22]?).getD (0,0), (row[41]?).getD (0,0), (row[52]?).getD (0,0), (row[62]?).getD (0,0), (row[71]?).getD (0,0), (row[79]?).getD (0,0), (row[84]?).getD (0,0), (row[86]?).getD (0,0), (row[88]?).getD (0,0)]
    rw [indexedLookup22 row, indexedLookup41 row, indexedLookup52 row, indexedLookup62 row, indexedLookup71 row, indexedLookup79 row, indexedLookup84 row, indexedLookup86 row, indexedLookup88 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (1,1), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (2,-4), patchState (literalDomain.zip row) (4,-4), patchState (literalDomain.zip row) (4,-3), patchState (literalDomain.zip row) (4,-2), patchState (literalDomain.zip row) (4,-1), patchState (literalDomain.zip row) (4,0), patchState (literalDomain.zip row) (4,1)] = encode [(row[57]?).getD (0,0), (row[60]?).getD (0,0), (row[62]?).getD (0,0), (row[79]?).getD (0,0), (row[80]?).getD (0,0), (row[81]?).getD (0,0), (row[82]?).getD (0,0), (row[83]?).getD (0,0), (row[84]?).getD (0,0)]
    rw [indexedLookup57 row, indexedLookup60 row, indexedLookup62 row, indexedLookup79 row, indexedLookup80 row, indexedLookup81 row, indexedLookup82 row, indexedLookup83 row, indexedLookup84 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-2,5), patchState (literalDomain.zip row) (-1,5), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (1,3), patchState (literalDomain.zip row) (2,2), patchState (literalDomain.zip row) (3,-5), patchState (literalDomain.zip row) (3,1), patchState (literalDomain.zip row) (4,-2), patchState (literalDomain.zip row) (4,0)] = encode [(row[29]?).getD (0,0), (row[39]?).getD (0,0), (row[49]?).getD (0,0), (row[59]?).getD (0,0), (row[68]?).getD (0,0), (row[70]?).getD (0,0), (row[76]?).getD (0,0), (row[81]?).getD (0,0), (row[83]?).getD (0,0)]
    rw [indexedLookup29 row, indexedLookup39 row, indexedLookup49 row, indexedLookup59 row, indexedLookup68 row, indexedLookup70 row, indexedLookup76 row, indexedLookup81 row, indexedLookup83 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-5,4), patchState (literalDomain.zip row) (-4,4), patchState (literalDomain.zip row) (-3,4), patchState (literalDomain.zip row) (-2,4), patchState (literalDomain.zip row) (-1,4), patchState (literalDomain.zip row) (0,4), patchState (literalDomain.zip row) (1,-5), patchState (literalDomain.zip row) (5,-1)] = encode [(row[4]?).getD (0,0), (row[11]?).getD (0,0), (row[19]?).getD (0,0), (row[28]?).getD (0,0), (row[38]?).getD (0,0), (row[49]?).getD (0,0), (row[51]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup4 row, indexedLookup11 row, indexedLookup19 row, indexedLookup28 row, indexedLookup38 row, indexedLookup49 row, indexedLookup51 row, indexedLookup89 row]
  · intro row
    change encode [patchState (literalDomain.zip row) (-4,2), patchState (literalDomain.zip row) (1,4), patchState (literalDomain.zip row) (5,-1)] = encode [(row[9]?).getD (0,0), (row[60]?).getD (0,0), (row[89]?).getD (0,0)]
    rw [indexedLookup9 row, indexedLookup60 row, indexedLookup89 row]

end SpectreFinite.HexSearch.RadiusFivePruning
