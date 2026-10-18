module

public import SpectreFinite.RadiusFourPruningIndexedSignatures

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFourPruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem indexedLookup2 (row : List State) : patchState (literalDomain.zip row) (-4,2) = (row[2]?).getD (0,0) := patchState_zip_index literalDomain row (-4,2) 2 (by decide) (by decide)
theorem indexedLookup7 (row : List State) : patchState (literalDomain.zip row) (-3,1) = (row[7]?).getD (0,0) := patchState_zip_index literalDomain row (-3,1) 7 (by decide) (by decide)
theorem indexedLookup8 (row : List State) : patchState (literalDomain.zip row) (-3,2) = (row[8]?).getD (0,0) := patchState_zip_index literalDomain row (-3,2) 8 (by decide) (by decide)
theorem indexedLookup11 (row : List State) : patchState (literalDomain.zip row) (-2,-2) = (row[11]?).getD (0,0) := patchState_zip_index literalDomain row (-2,-2) 11 (by decide) (by decide)
theorem indexedLookup12 (row : List State) : patchState (literalDomain.zip row) (-2,-1) = (row[12]?).getD (0,0) := patchState_zip_index literalDomain row (-2,-1) 12 (by decide) (by decide)
theorem indexedLookup13 (row : List State) : patchState (literalDomain.zip row) (-2,0) = (row[13]?).getD (0,0) := patchState_zip_index literalDomain row (-2,0) 13 (by decide) (by decide)
theorem indexedLookup14 (row : List State) : patchState (literalDomain.zip row) (-2,1) = (row[14]?).getD (0,0) := patchState_zip_index literalDomain row (-2,1) 14 (by decide) (by decide)
theorem indexedLookup15 (row : List State) : patchState (literalDomain.zip row) (-2,2) = (row[15]?).getD (0,0) := patchState_zip_index literalDomain row (-2,2) 15 (by decide) (by decide)
theorem indexedLookup16 (row : List State) : patchState (literalDomain.zip row) (-2,3) = (row[16]?).getD (0,0) := patchState_zip_index literalDomain row (-2,3) 16 (by decide) (by decide)
theorem indexedLookup17 (row : List State) : patchState (literalDomain.zip row) (-2,4) = (row[17]?).getD (0,0) := patchState_zip_index literalDomain row (-2,4) 17 (by decide) (by decide)
theorem indexedLookup18 (row : List State) : patchState (literalDomain.zip row) (-1,-3) = (row[18]?).getD (0,0) := patchState_zip_index literalDomain row (-1,-3) 18 (by decide) (by decide)
theorem indexedLookup19 (row : List State) : patchState (literalDomain.zip row) (-1,-2) = (row[19]?).getD (0,0) := patchState_zip_index literalDomain row (-1,-2) 19 (by decide) (by decide)
theorem indexedLookup20 (row : List State) : patchState (literalDomain.zip row) (-1,-1) = (row[20]?).getD (0,0) := patchState_zip_index literalDomain row (-1,-1) 20 (by decide) (by decide)
theorem indexedLookup21 (row : List State) : patchState (literalDomain.zip row) (-1,0) = (row[21]?).getD (0,0) := patchState_zip_index literalDomain row (-1,0) 21 (by decide) (by decide)
theorem indexedLookup22 (row : List State) : patchState (literalDomain.zip row) (-1,1) = (row[22]?).getD (0,0) := patchState_zip_index literalDomain row (-1,1) 22 (by decide) (by decide)
theorem indexedLookup23 (row : List State) : patchState (literalDomain.zip row) (-1,2) = (row[23]?).getD (0,0) := patchState_zip_index literalDomain row (-1,2) 23 (by decide) (by decide)
theorem indexedLookup24 (row : List State) : patchState (literalDomain.zip row) (-1,3) = (row[24]?).getD (0,0) := patchState_zip_index literalDomain row (-1,3) 24 (by decide) (by decide)
theorem indexedLookup28 (row : List State) : patchState (literalDomain.zip row) (0,-2) = (row[28]?).getD (0,0) := patchState_zip_index literalDomain row (0,-2) 28 (by decide) (by decide)
theorem indexedLookup29 (row : List State) : patchState (literalDomain.zip row) (0,-1) = (row[29]?).getD (0,0) := patchState_zip_index literalDomain row (0,-1) 29 (by decide) (by decide)
theorem indexedLookup30 (row : List State) : patchState (literalDomain.zip row) (0,0) = (row[30]?).getD (0,0) := patchState_zip_index literalDomain row (0,0) 30 (by decide) (by decide)
theorem indexedLookup31 (row : List State) : patchState (literalDomain.zip row) (0,1) = (row[31]?).getD (0,0) := patchState_zip_index literalDomain row (0,1) 31 (by decide) (by decide)
theorem indexedLookup32 (row : List State) : patchState (literalDomain.zip row) (0,2) = (row[32]?).getD (0,0) := patchState_zip_index literalDomain row (0,2) 32 (by decide) (by decide)
theorem indexedLookup36 (row : List State) : patchState (literalDomain.zip row) (1,-3) = (row[36]?).getD (0,0) := patchState_zip_index literalDomain row (1,-3) 36 (by decide) (by decide)
theorem indexedLookup37 (row : List State) : patchState (literalDomain.zip row) (1,-2) = (row[37]?).getD (0,0) := patchState_zip_index literalDomain row (1,-2) 37 (by decide) (by decide)
theorem indexedLookup38 (row : List State) : patchState (literalDomain.zip row) (1,-1) = (row[38]?).getD (0,0) := patchState_zip_index literalDomain row (1,-1) 38 (by decide) (by decide)
theorem indexedLookup39 (row : List State) : patchState (literalDomain.zip row) (1,0) = (row[39]?).getD (0,0) := patchState_zip_index literalDomain row (1,0) 39 (by decide) (by decide)
theorem indexedLookup40 (row : List State) : patchState (literalDomain.zip row) (1,1) = (row[40]?).getD (0,0) := patchState_zip_index literalDomain row (1,1) 40 (by decide) (by decide)
theorem indexedLookup41 (row : List State) : patchState (literalDomain.zip row) (1,2) = (row[41]?).getD (0,0) := patchState_zip_index literalDomain row (1,2) 41 (by decide) (by decide)
theorem indexedLookup43 (row : List State) : patchState (literalDomain.zip row) (2,-4) = (row[43]?).getD (0,0) := patchState_zip_index literalDomain row (2,-4) 43 (by decide) (by decide)
theorem indexedLookup44 (row : List State) : patchState (literalDomain.zip row) (2,-3) = (row[44]?).getD (0,0) := patchState_zip_index literalDomain row (2,-3) 44 (by decide) (by decide)
theorem indexedLookup45 (row : List State) : patchState (literalDomain.zip row) (2,-2) = (row[45]?).getD (0,0) := patchState_zip_index literalDomain row (2,-2) 45 (by decide) (by decide)
theorem indexedLookup46 (row : List State) : patchState (literalDomain.zip row) (2,-1) = (row[46]?).getD (0,0) := patchState_zip_index literalDomain row (2,-1) 46 (by decide) (by decide)
theorem indexedLookup47 (row : List State) : patchState (literalDomain.zip row) (2,0) = (row[47]?).getD (0,0) := patchState_zip_index literalDomain row (2,0) 47 (by decide) (by decide)
theorem indexedLookup48 (row : List State) : patchState (literalDomain.zip row) (2,1) = (row[48]?).getD (0,0) := patchState_zip_index literalDomain row (2,1) 48 (by decide) (by decide)
theorem indexedLookup49 (row : List State) : patchState (literalDomain.zip row) (2,2) = (row[49]?).getD (0,0) := patchState_zip_index literalDomain row (2,2) 49 (by decide) (by decide)
theorem indexedLookup52 (row : List State) : patchState (literalDomain.zip row) (3,-2) = (row[52]?).getD (0,0) := patchState_zip_index literalDomain row (3,-2) 52 (by decide) (by decide)
theorem indexedLookup53 (row : List State) : patchState (literalDomain.zip row) (3,-1) = (row[53]?).getD (0,0) := patchState_zip_index literalDomain row (3,-1) 53 (by decide) (by decide)
theorem indexedLookup58 (row : List State) : patchState (literalDomain.zip row) (4,-2) = (row[58]?).getD (0,0) := patchState_zip_index literalDomain row (4,-2) 58 (by decide) (by decide)

end SpectreFinite.HexSearch.RadiusFourPruning
