module

public import Mathlib.Tactic.FinCases
public import SparseMonotiles.CoarseContactCertificates5Rows
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed000
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed001
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed002
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed003
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed004
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed005
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed006
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed007
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed008
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed009
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed010
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed011
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed012
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed013
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed014
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed015
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed016
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed017
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed018
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed019
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed020
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed021
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed022
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed023
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed024
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed025
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed026
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed027
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed028
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed029
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed030
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed031
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed032
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed033
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed034
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed035
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed036
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed037
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed038
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed039
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed040
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed041
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed042
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed043
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed044
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed045
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed046
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed047
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed048
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed049
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed050
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed051
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed052
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed053
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed054
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed055
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed056
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed057
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed058
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed059
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed060
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed061
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed062
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed063
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed064
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed065
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed066
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed067
public import SparseMonotiles.CoarseContactCertificates5PackedRows.Packed068

@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def packedRowLookup (a : RowAddress) : ℕ :=
  (if a.1.val < 34 then (if a.1.val < 17 then (if a.1.val < 8 then (if a.1.val < 4 then (if a.1.val < 2 then (if a.1.val < 1 then packedRows000 else packedRows001) else (if a.1.val < 3 then packedRows002 else packedRows003)) else (if a.1.val < 6 then (if a.1.val < 5 then packedRows004 else packedRows005) else (if a.1.val < 7 then packedRows006 else packedRows007))) else (if a.1.val < 12 then (if a.1.val < 10 then (if a.1.val < 9 then packedRows008 else packedRows009) else (if a.1.val < 11 then packedRows010 else packedRows011)) else (if a.1.val < 14 then (if a.1.val < 13 then packedRows012 else packedRows013) else (if a.1.val < 15 then packedRows014 else (if a.1.val < 16 then packedRows015 else packedRows016))))) else (if a.1.val < 25 then (if a.1.val < 21 then (if a.1.val < 19 then (if a.1.val < 18 then packedRows017 else packedRows018) else (if a.1.val < 20 then packedRows019 else packedRows020)) else (if a.1.val < 23 then (if a.1.val < 22 then packedRows021 else packedRows022) else (if a.1.val < 24 then packedRows023 else packedRows024))) else (if a.1.val < 29 then (if a.1.val < 27 then (if a.1.val < 26 then packedRows025 else packedRows026) else (if a.1.val < 28 then packedRows027 else packedRows028)) else (if a.1.val < 31 then (if a.1.val < 30 then packedRows029 else packedRows030) else (if a.1.val < 32 then packedRows031 else (if a.1.val < 33 then packedRows032 else packedRows033)))))) else (if a.1.val < 51 then (if a.1.val < 42 then (if a.1.val < 38 then (if a.1.val < 36 then (if a.1.val < 35 then packedRows034 else packedRows035) else (if a.1.val < 37 then packedRows036 else packedRows037)) else (if a.1.val < 40 then (if a.1.val < 39 then packedRows038 else packedRows039) else (if a.1.val < 41 then packedRows040 else packedRows041))) else (if a.1.val < 46 then (if a.1.val < 44 then (if a.1.val < 43 then packedRows042 else packedRows043) else (if a.1.val < 45 then packedRows044 else packedRows045)) else (if a.1.val < 48 then (if a.1.val < 47 then packedRows046 else packedRows047) else (if a.1.val < 49 then packedRows048 else (if a.1.val < 50 then packedRows049 else packedRows050))))) else (if a.1.val < 60 then (if a.1.val < 55 then (if a.1.val < 53 then (if a.1.val < 52 then packedRows051 else packedRows052) else (if a.1.val < 54 then packedRows053 else packedRows054)) else (if a.1.val < 57 then (if a.1.val < 56 then packedRows055 else packedRows056) else (if a.1.val < 58 then packedRows057 else (if a.1.val < 59 then packedRows058 else packedRows059)))) else (if a.1.val < 64 then (if a.1.val < 62 then (if a.1.val < 61 then packedRows060 else packedRows061) else (if a.1.val < 63 then packedRows062 else packedRows063)) else (if a.1.val < 66 then (if a.1.val < 65 then packedRows064 else packedRows065) else (if a.1.val < 67 then packedRows066 else (if a.1.val < 68 then packedRows067 else packedRows068))))))) a.2
theorem packedRow_bound (a : RowAddress) : PackedRepresents (packedRowLookup a) (rowPose a) := by
  rcases a with ⟨i, j⟩
  fin_cases i
  · exact packedRows000_bound j
  · exact packedRows001_bound j
  · exact packedRows002_bound j
  · exact packedRows003_bound j
  · exact packedRows004_bound j
  · exact packedRows005_bound j
  · exact packedRows006_bound j
  · exact packedRows007_bound j
  · exact packedRows008_bound j
  · exact packedRows009_bound j
  · exact packedRows010_bound j
  · exact packedRows011_bound j
  · exact packedRows012_bound j
  · exact packedRows013_bound j
  · exact packedRows014_bound j
  · exact packedRows015_bound j
  · exact packedRows016_bound j
  · exact packedRows017_bound j
  · exact packedRows018_bound j
  · exact packedRows019_bound j
  · exact packedRows020_bound j
  · exact packedRows021_bound j
  · exact packedRows022_bound j
  · exact packedRows023_bound j
  · exact packedRows024_bound j
  · exact packedRows025_bound j
  · exact packedRows026_bound j
  · exact packedRows027_bound j
  · exact packedRows028_bound j
  · exact packedRows029_bound j
  · exact packedRows030_bound j
  · exact packedRows031_bound j
  · exact packedRows032_bound j
  · exact packedRows033_bound j
  · exact packedRows034_bound j
  · exact packedRows035_bound j
  · exact packedRows036_bound j
  · exact packedRows037_bound j
  · exact packedRows038_bound j
  · exact packedRows039_bound j
  · exact packedRows040_bound j
  · exact packedRows041_bound j
  · exact packedRows042_bound j
  · exact packedRows043_bound j
  · exact packedRows044_bound j
  · exact packedRows045_bound j
  · exact packedRows046_bound j
  · exact packedRows047_bound j
  · exact packedRows048_bound j
  · exact packedRows049_bound j
  · exact packedRows050_bound j
  · exact packedRows051_bound j
  · exact packedRows052_bound j
  · exact packedRows053_bound j
  · exact packedRows054_bound j
  · exact packedRows055_bound j
  · exact packedRows056_bound j
  · exact packedRows057_bound j
  · exact packedRows058_bound j
  · exact packedRows059_bound j
  · exact packedRows060_bound j
  · exact packedRows061_bound j
  · exact packedRows062_bound j
  · exact packedRows063_bound j
  · exact packedRows064_bound j
  · exact packedRows065_bound j
  · exact packedRows066_bound j
  · exact packedRows067_bound j
  · exact packedRows068_bound j
#print axioms packedRow_bound
end SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5
