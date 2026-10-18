module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! Exact integer metric certificates for the two optimized 4D reference
pyramids. The recipe is bound to rational coordinates below. Geometric
extreme-point and affine-span identification are separate obligations. -/
namespace SpectreGeometry.ProductKeyReference

def referenceDenominator : ℤ := 44485841400000

def integerFingerprint (v : Fin 9 → Fin 4 → ℤ) (i : Fin 9) : ℤ :=
  ∑ j, ∑ k, (v i k - v j k)^2

def referenceVertices1 : Fin 9 → Fin 4 → ℤ :=
  ![![0, 0, 0, 255255],
    ![-370715345, -158878005, -85549695, 0],
    ![222429207, -158878005, -85549695, 0],
    ![-370715345, 101104185, -85549695, 0],
    ![222429207, 101104185, -85549695, 0],
    ![-370715345, -158878005, 65420355, 0],
    ![222429207, -158878005, 65420355, 0],
    ![-370715345, 101104185, 65420355, 0],
    ![222429207, 101104185, 65420355, 0]]

def referenceRationalVertices1 : Fin 9 → Fin 4 → ℚ :=
  ![![0, 0, 0, 1 / (40000 * 4357)],
    ![-(1 / (40000 * 3)), -(1 / (40000 * 7)), -(1 / (40000 * 13)), 0],
    ![1 / (40000 * 5), -(1 / (40000 * 7)), -(1 / (40000 * 13)), 0],
    ![-(1 / (40000 * 3)), 1 / (40000 * 11), -(1 / (40000 * 13)), 0],
    ![1 / (40000 * 5), 1 / (40000 * 11), -(1 / (40000 * 13)), 0],
    ![-(1 / (40000 * 3)), -(1 / (40000 * 7)), 1 / (40000 * 17), 0],
    ![1 / (40000 * 5), -(1 / (40000 * 7)), 1 / (40000 * 17), 0],
    ![-(1 / (40000 * 3)), 1 / (40000 * 11), 1 / (40000 * 17), 0],
    ![1 / (40000 * 5), 1 / (40000 * 11), 1 / (40000 * 17), 0]]

def referenceFingerprint1 : Fin 9 → ℤ := ![935870397262244896, 1938803521686874316, 1850848406795054140, 1923783357438608516, 1835828242546788340, 1935764594220607316, 1847809479328787140, 1920744429972341516, 1832789315080521340]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem reference1_rational_binding : ∀ i k,
    (referenceVertices1 i k : ℚ) / referenceDenominator = referenceRationalVertices1 i k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem reference1_fingerprint : ∀ i,
    integerFingerprint referenceVertices1 i = referenceFingerprint1 i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem reference1_fingerprint_injective : Function.Injective referenceFingerprint1 := by
  decide +kernel

theorem reference1_integerFingerprint_injective :
    Function.Injective (integerFingerprint referenceVertices1) := by
  intro i k h
  apply reference1_fingerprint_injective
  simpa only [reference1_fingerprint] using h

def referenceVertices2 : Fin 9 → Fin 4 → ℤ :=
  ![![0, 0, 0, 510510],
    ![-370715345, -158878005, -85549695, 0],
    ![222429207, -158878005, -85549695, 0],
    ![-370715345, 101104185, -85549695, 0],
    ![222429207, 101104185, -85549695, 0],
    ![-370715345, -158878005, 65420355, 0],
    ![222429207, -158878005, 65420355, 0],
    ![-370715345, 101104185, 65420355, 0],
    ![222429207, 101104185, 65420355, 0]]

def referenceRationalVertices2 : Fin 9 → Fin 4 → ℚ :=
  ![![0, 0, 0, 2 / (40000 * 4357)],
    ![-(1 / (40000 * 3)), -(1 / (40000 * 7)), -(1 / (40000 * 13)), 0],
    ![1 / (40000 * 5), -(1 / (40000 * 7)), -(1 / (40000 * 13)), 0],
    ![-(1 / (40000 * 3)), 1 / (40000 * 11), -(1 / (40000 * 13)), 0],
    ![1 / (40000 * 5), 1 / (40000 * 11), -(1 / (40000 * 13)), 0],
    ![-(1 / (40000 * 3)), -(1 / (40000 * 7)), 1 / (40000 * 17), 0],
    ![1 / (40000 * 5), -(1 / (40000 * 7)), 1 / (40000 * 17), 0],
    ![-(1 / (40000 * 3)), 1 / (40000 * 11), 1 / (40000 * 17), 0],
    ![1 / (40000 * 5), 1 / (40000 * 11), 1 / (40000 * 17), 0]]

def referenceFingerprint2 : Fin 9 → ℤ := ![935871960985005496, 1938803717152219391, 1850848602260399215, 1923783552903953591, 1835828438012133415, 1935764789685952391, 1847809674794132215, 1920744625437686591, 1832789510545866415]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem reference2_rational_binding : ∀ i k,
    (referenceVertices2 i k : ℚ) / referenceDenominator = referenceRationalVertices2 i k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem reference2_fingerprint : ∀ i,
    integerFingerprint referenceVertices2 i = referenceFingerprint2 i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem reference2_fingerprint_injective : Function.Injective referenceFingerprint2 := by
  decide +kernel

theorem reference2_integerFingerprint_injective :
    Function.Injective (integerFingerprint referenceVertices2) := by
  intro i k h
  apply reference2_fingerprint_injective
  simpa only [reference2_fingerprint] using h

end SpectreGeometry.ProductKeyReference
