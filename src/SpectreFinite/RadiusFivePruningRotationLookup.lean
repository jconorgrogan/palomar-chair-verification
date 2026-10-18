module

public import SpectreFinite.RadiusFivePruningIndexedSignatures

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFivePruning
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem indexedLookup18 (row : List State) : patchState (literalDomain.zip row) (-3,3) = (row[18]?).getD (0,0) := patchState_zip_index literalDomain row (-3,3) 18 (by decide) (by decide)
theorem indexedLookup23 (row : List State) : patchState (literalDomain.zip row) (-2,-1) = (row[23]?).getD (0,0) := patchState_zip_index literalDomain row (-2,-1) 23 (by decide) (by decide)
theorem indexedLookup24 (row : List State) : patchState (literalDomain.zip row) (-2,0) = (row[24]?).getD (0,0) := patchState_zip_index literalDomain row (-2,0) 24 (by decide) (by decide)
theorem indexedLookup25 (row : List State) : patchState (literalDomain.zip row) (-2,1) = (row[25]?).getD (0,0) := patchState_zip_index literalDomain row (-2,1) 25 (by decide) (by decide)
theorem indexedLookup26 (row : List State) : patchState (literalDomain.zip row) (-2,2) = (row[26]?).getD (0,0) := patchState_zip_index literalDomain row (-2,2) 26 (by decide) (by decide)
theorem indexedLookup32 (row : List State) : patchState (literalDomain.zip row) (-1,-2) = (row[32]?).getD (0,0) := patchState_zip_index literalDomain row (-1,-2) 32 (by decide) (by decide)
theorem indexedLookup33 (row : List State) : patchState (literalDomain.zip row) (-1,-1) = (row[33]?).getD (0,0) := patchState_zip_index literalDomain row (-1,-1) 33 (by decide) (by decide)
theorem indexedLookup34 (row : List State) : patchState (literalDomain.zip row) (-1,0) = (row[34]?).getD (0,0) := patchState_zip_index literalDomain row (-1,0) 34 (by decide) (by decide)
theorem indexedLookup35 (row : List State) : patchState (literalDomain.zip row) (-1,1) = (row[35]?).getD (0,0) := patchState_zip_index literalDomain row (-1,1) 35 (by decide) (by decide)
theorem indexedLookup44 (row : List State) : patchState (literalDomain.zip row) (0,-1) = (row[44]?).getD (0,0) := patchState_zip_index literalDomain row (0,-1) 44 (by decide) (by decide)
theorem indexedLookup45 (row : List State) : patchState (literalDomain.zip row) (0,0) = (row[45]?).getD (0,0) := patchState_zip_index literalDomain row (0,0) 45 (by decide) (by decide)
theorem indexedLookup46 (row : List State) : patchState (literalDomain.zip row) (0,1) = (row[46]?).getD (0,0) := patchState_zip_index literalDomain row (0,1) 46 (by decide) (by decide)
theorem indexedLookup47 (row : List State) : patchState (literalDomain.zip row) (0,2) = (row[47]?).getD (0,0) := patchState_zip_index literalDomain row (0,2) 47 (by decide) (by decide)
theorem indexedLookup55 (row : List State) : patchState (literalDomain.zip row) (1,-1) = (row[55]?).getD (0,0) := patchState_zip_index literalDomain row (1,-1) 55 (by decide) (by decide)
theorem indexedLookup56 (row : List State) : patchState (literalDomain.zip row) (1,0) = (row[56]?).getD (0,0) := patchState_zip_index literalDomain row (1,0) 56 (by decide) (by decide)
theorem indexedLookup65 (row : List State) : patchState (literalDomain.zip row) (2,-1) = (row[65]?).getD (0,0) := patchState_zip_index literalDomain row (2,-1) 65 (by decide) (by decide)
theorem indexedLookup74 (row : List State) : patchState (literalDomain.zip row) (3,-1) = (row[74]?).getD (0,0) := patchState_zip_index literalDomain row (3,-1) 74 (by decide) (by decide)
theorem indexedLookup75 (row : List State) : patchState (literalDomain.zip row) (3,0) = (row[75]?).getD (0,0) := patchState_zip_index literalDomain row (3,0) 75 (by decide) (by decide)

end SpectreFinite.HexSearch.RadiusFivePruning
