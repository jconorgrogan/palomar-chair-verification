module

public import Mathlib.Tactic.FinCases
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows000
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows001
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows002
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows003
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows004
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows005
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows006
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows007
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows008
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows009
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows010
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows011
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows012
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows013
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows014
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows015
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows016
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows017
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows018
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows019
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows020
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows021
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows022
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows023
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows024
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows025
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows026
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows027
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows028
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows029
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows030
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows031
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows032
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows033
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows034
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows035
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows036
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows037
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows038
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows039
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows040
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows041
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows042
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows043
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows044
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows045
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows046
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows047
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows048
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows049
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows050
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows051
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows052
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows053
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows054
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows055
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows056
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows057
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows058
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows059
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows060
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows061
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows062
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows063
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows064
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows065
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows066
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows067
public import SparseMonotiles.CoarseContactCertificates5Chunks.Rows068

@[expose] public section

namespace SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev RowAddress := Fin 69 × Fin 256
def rowLookup (a : RowAddress) : CoarseRow 5 :=
  ((if a.1.val < 34 then (if a.1.val < 17 then (if a.1.val < 8 then (if a.1.val < 4 then (if a.1.val < 2 then (if a.1.val < 1 then Rows000 else Rows001) else (if a.1.val < 3 then Rows002 else Rows003)) else (if a.1.val < 6 then (if a.1.val < 5 then Rows004 else Rows005) else (if a.1.val < 7 then Rows006 else Rows007))) else (if a.1.val < 12 then (if a.1.val < 10 then (if a.1.val < 9 then Rows008 else Rows009) else (if a.1.val < 11 then Rows010 else Rows011)) else (if a.1.val < 14 then (if a.1.val < 13 then Rows012 else Rows013) else (if a.1.val < 15 then Rows014 else (if a.1.val < 16 then Rows015 else Rows016))))) else (if a.1.val < 25 then (if a.1.val < 21 then (if a.1.val < 19 then (if a.1.val < 18 then Rows017 else Rows018) else (if a.1.val < 20 then Rows019 else Rows020)) else (if a.1.val < 23 then (if a.1.val < 22 then Rows021 else Rows022) else (if a.1.val < 24 then Rows023 else Rows024))) else (if a.1.val < 29 then (if a.1.val < 27 then (if a.1.val < 26 then Rows025 else Rows026) else (if a.1.val < 28 then Rows027 else Rows028)) else (if a.1.val < 31 then (if a.1.val < 30 then Rows029 else Rows030) else (if a.1.val < 32 then Rows031 else (if a.1.val < 33 then Rows032 else Rows033)))))) else (if a.1.val < 51 then (if a.1.val < 42 then (if a.1.val < 38 then (if a.1.val < 36 then (if a.1.val < 35 then Rows034 else Rows035) else (if a.1.val < 37 then Rows036 else Rows037)) else (if a.1.val < 40 then (if a.1.val < 39 then Rows038 else Rows039) else (if a.1.val < 41 then Rows040 else Rows041))) else (if a.1.val < 46 then (if a.1.val < 44 then (if a.1.val < 43 then Rows042 else Rows043) else (if a.1.val < 45 then Rows044 else Rows045)) else (if a.1.val < 48 then (if a.1.val < 47 then Rows046 else Rows047) else (if a.1.val < 49 then Rows048 else (if a.1.val < 50 then Rows049 else Rows050))))) else (if a.1.val < 60 then (if a.1.val < 55 then (if a.1.val < 53 then (if a.1.val < 52 then Rows051 else Rows052) else (if a.1.val < 54 then Rows053 else Rows054)) else (if a.1.val < 57 then (if a.1.val < 56 then Rows055 else Rows056) else (if a.1.val < 58 then Rows057 else (if a.1.val < 59 then Rows058 else Rows059)))) else (if a.1.val < 64 then (if a.1.val < 62 then (if a.1.val < 61 then Rows060 else Rows061) else (if a.1.val < 63 then Rows062 else Rows063)) else (if a.1.val < 66 then (if a.1.val < 65 then Rows064 else Rows065) else (if a.1.val < 67 then Rows066 else (if a.1.val < 68 then Rows067 else Rows068))))))) a.2).toRow child
def rowPose (a : RowAddress) : Pose 5 := (rowLookup a).pose
theorem all_rows_valid (a : RowAddress) :
    (rowLookup a).witness.Valid C L (rowLookup a).pose := by
  rcases a with ⟨i, j⟩
  fin_cases i
  · exact Rows000_valid j
  · exact Rows001_valid j
  · exact Rows002_valid j
  · exact Rows003_valid j
  · exact Rows004_valid j
  · exact Rows005_valid j
  · exact Rows006_valid j
  · exact Rows007_valid j
  · exact Rows008_valid j
  · exact Rows009_valid j
  · exact Rows010_valid j
  · exact Rows011_valid j
  · exact Rows012_valid j
  · exact Rows013_valid j
  · exact Rows014_valid j
  · exact Rows015_valid j
  · exact Rows016_valid j
  · exact Rows017_valid j
  · exact Rows018_valid j
  · exact Rows019_valid j
  · exact Rows020_valid j
  · exact Rows021_valid j
  · exact Rows022_valid j
  · exact Rows023_valid j
  · exact Rows024_valid j
  · exact Rows025_valid j
  · exact Rows026_valid j
  · exact Rows027_valid j
  · exact Rows028_valid j
  · exact Rows029_valid j
  · exact Rows030_valid j
  · exact Rows031_valid j
  · exact Rows032_valid j
  · exact Rows033_valid j
  · exact Rows034_valid j
  · exact Rows035_valid j
  · exact Rows036_valid j
  · exact Rows037_valid j
  · exact Rows038_valid j
  · exact Rows039_valid j
  · exact Rows040_valid j
  · exact Rows041_valid j
  · exact Rows042_valid j
  · exact Rows043_valid j
  · exact Rows044_valid j
  · exact Rows045_valid j
  · exact Rows046_valid j
  · exact Rows047_valid j
  · exact Rows048_valid j
  · exact Rows049_valid j
  · exact Rows050_valid j
  · exact Rows051_valid j
  · exact Rows052_valid j
  · exact Rows053_valid j
  · exact Rows054_valid j
  · exact Rows055_valid j
  · exact Rows056_valid j
  · exact Rows057_valid j
  · exact Rows058_valid j
  · exact Rows059_valid j
  · exact Rows060_valid j
  · exact Rows061_valid j
  · exact Rows062_valid j
  · exact Rows063_valid j
  · exact Rows064_valid j
  · exact Rows065_valid j
  · exact Rows066_valid j
  · exact Rows067_valid j
  · exact Rows068_valid j
#print axioms all_rows_valid
end SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5
