module

public import PhysicalRegistration.KeyTent

@[expose] public section


/-!
Exact coordinate separation for the native registration tubes. The set
`coordinateTube` is a symmetric coordinate enclosure of the asymmetric
prime-key tube. All disjointness conclusions below are derived from center
coordinates and numerical widths; disjointness is never an input.

The native-site construction must still supply the integer normal planes,
integer-plus-half tangent facet centers, signed orbit offsets, and the
containment of each actual asymmetric tube in this coordinate enclosure.
-/

namespace PhysicalRegistration
open Set

variable {ι : Type*}

/-- Symmetric coordinate enclosure of a tube: normal half-width `rho`, and
uniform tangent coordinate half-width `eta`. -/
def coordinateTube (normal : ι) (center : ι → ℝ) (eta rho : ℝ) : Set (ι → ℝ) :=
  {x | |x normal - center normal| ≤ rho ∧
    ∀ j, j ≠ normal → |x j - center j| ≤ eta}

/-- A point in a native tangent support stays at distance strictly greater
than `1/4 - eta` from every integer plane, not just the two facet edges. -/
theorem native_tangent_distance_from_integer (b n : ℤ) (q v eta : ℝ)
    (hq : |q| < 1 / 4) (hv : |v| ≤ eta) :
    1 / 4 - eta < |(b : ℝ) + 1 / 2 + q + v - (n : ℝ)| := by
  have hm := key_support_facet_margin eta q v hq hv
  by_cases hnb : n ≤ b
  · have hnb' : (n : ℝ) ≤ b := by exact_mod_cast hnb
    have hlo : 1 / 4 - eta < (b : ℝ) + 1 / 2 + q + v - n := by
      linarith [hm.1]
    exact hlo.trans_le (le_abs_self _)
  · have hbn : b + 1 ≤ n := Int.add_one_le_iff.mpr (lt_of_not_ge hnb)
    have hbn' : (b : ℝ) + 1 ≤ n := by exact_mod_cast hbn
    have hhi : 1 / 4 - eta < -((b : ℝ) + 1 / 2 + q + v - n) := by
      linarith [hm.2]
    exact hhi.trans_le (neg_le_abs _)

/-- Different normal axes force one coordinate to be simultaneously close
to an integer plane and separated from every integer plane. -/
theorem coordinateTube_disjoint_of_different_normals
    (i j : ι) (c c' : ι → ℝ) (eta rho : ℝ)
    (hij : i ≠ j) (hwidth : eta + rho ≤ 1 / 4)
    (normalPlane : ℤ) (hnormal : c' j = normalPlane)
    (facetCell : ℤ) (offset : ℝ)
    (htangent : c j = (facetCell : ℝ) + 1 / 2 + offset)
    (hoffset : |offset| < 1 / 4) :
    Disjoint (coordinateTube i c eta rho) (coordinateTube j c' eta rho) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have hv : |x j - c j| ≤ eta := hx.2 j (Ne.symm hij)
  have hfar := native_tangent_distance_from_integer facetCell normalPlane
    offset (x j - c j) eta hoffset hv
  have heq : (facetCell : ℝ) + 1 / 2 + offset + (x j - c j) - normalPlane =
      x j - c' j := by rw [htangent, hnormal]; ring
  rw [heq] at hfar
  have hnear : |x j - c' j| ≤ rho := hx'.1
  linarith

/-- Any separating tangent coordinate suffices for disjointness of two
parallel coordinate tubes. This applies both within one facet and across
coplanar neighboring facets. -/
theorem coordinateTube_disjoint_of_tangent_gap
    (i j : ι) (c c' : ι → ℝ) (eta rho : ℝ)
    (hji : j ≠ i) (hgap : 2 * eta < |c j - c' j|) :
    Disjoint (coordinateTube i c eta rho) (coordinateTube i c' eta rho) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have h₁ := abs_le.mp (hx.2 j hji)
  have h₂ := abs_le.mp (hx'.2 j hji)
  have habs : |c j - c' j| ≤ 2 * eta := by
    apply abs_le.mpr
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  exact (not_lt_of_ge habs) hgap

/-- Any separating normal coordinate suffices for parallel tubes. -/
theorem coordinateTube_disjoint_of_normal_gap
    (i : ι) (c c' : ι → ℝ) (eta rho : ℝ)
    (hgap : 2 * rho < |c i - c' i|) :
    Disjoint (coordinateTube i c eta rho) (coordinateTube i c' eta rho) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have h₁ := abs_le.mp hx.1
  have h₂ := abs_le.mp hx'.1
  have habs : |c i - c' i| ≤ 2 * rho := by
    apply abs_le.mpr
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  exact (not_lt_of_ge habs) hgap

/-- Distinct integer coordinates have separation at least one. -/
theorem integer_coordinate_gap (a b : ℤ) (hab : a ≠ b) :
    (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℝ) + 1 ≤ b := by
      exact_mod_cast Int.add_one_le_iff.mpr h
    have hneg : (1 : ℝ) ≤ -((a : ℝ) - b) := by linarith
    exact hneg.trans (neg_le_abs _)
  · have h' : (b : ℝ) + 1 ≤ a := by
      exact_mod_cast Int.add_one_le_iff.mpr h
    have hpos : (1 : ℝ) ≤ (a : ℝ) - b := by linarith
    exact hpos.trans (le_abs_self _)

/-- Parallel distinct integer facet planes give disjoint enclosures as
soon as the total normal width is less than one. -/
theorem coordinateTube_disjoint_of_distinct_integer_planes
    (i : ι) (c c' : ι → ℝ) (eta rho : ℝ)
    (a b : ℤ) (ha : c i = a) (hb : c' i = b)
    (hab : a ≠ b) (hwidth : 2 * rho < 1) :
    Disjoint (coordinateTube i c eta rho) (coordinateTube i c' eta rho) := by
  apply coordinateTube_disjoint_of_normal_gap
  rw [ha, hb]
  exact hwidth.trans_le (integer_coordinate_gap a b hab)

/-- Distinct signed integer orbit numerators give the manuscript's exact
same-facet spacing lower bound. -/
theorem signed_orbit_coordinate_gap (d : ℝ) (hd : 0 < d)
    (b : ℝ) (k l : ℤ) (hkl : k ≠ l) :
    1 / (4 * d) ≤ |(b + (k : ℝ) / (4 * d)) - (b + (l : ℝ) / (4 * d))| := by
  have hgap := integer_coordinate_gap k l hkl
  have heq : (b + (k : ℝ) / (4 * d)) - (b + (l : ℝ) / (4 * d)) =
      ((k : ℝ) - l) / (4 * d) := by ring
  rw [heq, abs_div, abs_of_pos (by positivity : 0 < 4 * d)]
  exact div_le_div_of_nonneg_right hgap (by positivity)

/-- Integer-separated tangent cells retain a gap exceeding one half after
both signed orbit offsets, since each offset has magnitude below one fourth. -/
theorem distinct_facet_tangent_center_gap (a b : ℤ) (q q' : ℝ)
    (hab : a ≠ b) (hq : |q| < 1 / 4) (hq' : |q'| < 1 / 4) :
    (1 / 2 : ℝ) < |((a : ℝ) + 1 / 2 + q) - ((b : ℝ) + 1 / 2 + q')| := by
  rcases abs_lt.mp hq with ⟨hqlo, hqhi⟩
  rcases abs_lt.mp hq' with ⟨hq'lo, hq'hi⟩
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℝ) + 1 ≤ b := by
      exact_mod_cast Int.add_one_le_iff.mpr h
    have hneg : (1 / 2 : ℝ) <
        -(((a : ℝ) + 1 / 2 + q) - ((b : ℝ) + 1 / 2 + q')) := by linarith
    exact hneg.trans_le (neg_le_abs _)
  · have h' : (b : ℝ) + 1 ≤ a := by
      exact_mod_cast Int.add_one_le_iff.mpr h
    have hpos : (1 / 2 : ℝ) <
        ((a : ℝ) + 1 / 2 + q) - ((b : ℝ) + 1 / 2 + q') := by linarith
    exact hpos.trans_le (le_abs_self _)

/-- The three numerical separation inequalities, checked at the exact
manuscript choices eta=1/(128d), rho=1/(32d). -/
theorem chosen_tube_width_bounds (d : ℝ) (hd : 3 ≤ d) :
    1 / (128 * d) + 1 / (32 * d) ≤ 1 / 4 ∧
      2 * (1 / (32 * d)) < 1 ∧
      2 * (1 / (128 * d)) < 1 / (4 * d) := by
  have hd0 : 0 < d := by linarith
  have h₁ : 1 / (128 * d) + 1 / (32 * d) = 5 / (128 * d) := by
    field_simp
    ring
  have h₂ : 2 * (1 / (32 * d)) = 1 / (16 * d) := by
    field_simp
    ring
  have h₃ : 2 * (1 / (128 * d)) = 1 / (64 * d) := by
    field_simp
    ring
  constructor
  · rw [h₁]
    apply (div_le_iff₀ (by positivity : 0 < 128 * d)).mpr
    linarith
  constructor
  · rw [h₂]
    apply (div_lt_iff₀ (by positivity : 0 < 16 * d)).mpr
    linarith
  · rw [h₃]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- Different-axis separation at the exact construction widths. -/
theorem native_coordinateTube_disjoint_of_different_normals
    (d : ℝ) (hd : 3 ≤ d) (i j : ι) (c c' : ι → ℝ)
    (hij : i ≠ j) (normalPlane : ℤ) (hnormal : c' j = normalPlane)
    (facetCell : ℤ) (offset : ℝ)
    (htangent : c j = (facetCell : ℝ) + 1 / 2 + offset)
    (hoffset : |offset| < 1 / 4) :
    Disjoint (coordinateTube i c (1 / (128 * d)) (1 / (32 * d)))
      (coordinateTube j c' (1 / (128 * d)) (1 / (32 * d))) :=
  coordinateTube_disjoint_of_different_normals i j c c' _ _ hij
    (chosen_tube_width_bounds d hd).1 normalPlane hnormal facetCell offset htangent hoffset

/-- Parallel-plane separation at the exact construction widths. -/
theorem native_coordinateTube_disjoint_of_distinct_integer_planes
    (d : ℝ) (hd : 3 ≤ d) (i : ι) (c c' : ι → ℝ)
    (a b : ℤ) (ha : c i = a) (hb : c' i = b) (hab : a ≠ b) :
    Disjoint (coordinateTube i c (1 / (128 * d)) (1 / (32 * d)))
      (coordinateTube i c' (1 / (128 * d)) (1 / (32 * d))) :=
  coordinateTube_disjoint_of_distinct_integer_planes i c c' _ _ a b ha hb hab
    (chosen_tube_width_bounds d hd).2.1

/-- Same-facet separation from two distinct signed orbit numerators at one
tangent coordinate. There is no assumed disjointness or assumed gap. -/
theorem native_coordinateTube_disjoint_of_distinct_orbit_coordinates
    (d : ℝ) (hd : 3 ≤ d) (i j : ι) (c c' : ι → ℝ) (hji : j ≠ i)
    (b : ℝ) (k l : ℤ)
    (hc : c j = b + (k : ℝ) / (4 * d))
    (hc' : c' j = b + (l : ℝ) / (4 * d)) (hkl : k ≠ l) :
    Disjoint (coordinateTube i c (1 / (128 * d)) (1 / (32 * d)))
      (coordinateTube i c' (1 / (128 * d)) (1 / (32 * d))) := by
  apply coordinateTube_disjoint_of_tangent_gap i j c c' _ _ hji
  rw [hc, hc']
  exact (chosen_tube_width_bounds d hd).2.2.trans_le
    (signed_orbit_coordinate_gap d (by linarith) b k l hkl)

/-- Coplanar distinct unit facets are separated in any tangent coordinate
where their integer cell origins differ, including adjacent facets. -/
theorem native_coordinateTube_disjoint_of_distinct_tangent_cells
    (d : ℝ) (hd : 3 ≤ d) (i j : ι) (c c' : ι → ℝ) (hji : j ≠ i)
    (a b : ℤ) (q q' : ℝ)
    (hc : c j = (a : ℝ) + 1 / 2 + q)
    (hc' : c' j = (b : ℝ) + 1 / 2 + q')
    (hab : a ≠ b) (hq : |q| < 1 / 4) (hq' : |q'| < 1 / 4) :
    Disjoint (coordinateTube i c (1 / (128 * d)) (1 / (32 * d)))
      (coordinateTube i c' (1 / (128 * d)) (1 / (32 * d))) := by
  apply coordinateTube_disjoint_of_tangent_gap i j c c' _ _ hji
  rw [hc, hc']
  have hwidth := (chosen_tube_width_bounds d hd).1
  have hrho : 0 ≤ 1 / (32 * d) := by positivity
  have hhalf : 2 * (1 / (128 * d)) ≤ 1 / 2 := by linarith
  exact hhalf.trans_lt (distinct_facet_tangent_center_gap a b q q' hab hq hq')

/-- The closed asymmetric footprint, including its zero-height boundary,
is contained in the symmetric radius-eta coordinate interval. -/
theorem closed_asymmetric_footprint_coordinate_bound
    (eta pMinus pPlus v : ℝ) (heta : 0 ≤ eta)
    (hm : 1 ≤ pMinus) (hp : 1 ≤ pPlus)
    (hv : -eta / pMinus ≤ v ∧ v ≤ eta / pPlus) : |v| ≤ eta := by
  have hm0 : 0 < pMinus := by linarith
  have hp0 : 0 < pPlus := by linarith
  have hmdiv : eta / pMinus ≤ eta :=
    (div_le_iff₀ hm0).mpr (by nlinarith)
  have hpdiv : eta / pPlus ≤ eta :=
    (div_le_iff₀ hp0).mpr (by nlinarith)
  apply abs_le.mpr
  rw [neg_div] at hv
  constructor <;> linarith [hv.1, hv.2]

/-- Axis-aligned asymmetric coordinate tube. Signed permutations of the
native tangent box can be written this way by permuting the slope parameters
and swapping the minus/plus parameters at every reversed coordinate. -/
def asymmetricCoordinateTube (normal : ι) (center : ι → ℝ)
    (pMinus pPlus : ι → ℝ) (eta rho : ℝ) : Set (ι → ℝ) :=
  {x | |x normal - center normal| ≤ rho ∧
    ∀ j, j ≠ normal →
      -eta / pMinus j ≤ x j - center j ∧ x j - center j ≤ eta / pPlus j}

/-- Coordinate containment derives from the actual asymmetric endpoints;
it does not assume that the supports are already separated. -/
theorem asymmetricCoordinateTube_subset_coordinateTube
    (normal : ι) (center : ι → ℝ) (pMinus pPlus : ι → ℝ)
    (eta rho : ℝ) (heta : 0 ≤ eta)
    (hm : ∀ j, j ≠ normal → 1 ≤ pMinus j)
    (hp : ∀ j, j ≠ normal → 1 ≤ pPlus j) :
    asymmetricCoordinateTube normal center pMinus pPlus eta rho ⊆
      coordinateTube normal center eta rho := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro j hj
  exact closed_asymmetric_footprint_coordinate_bound eta (pMinus j) (pPlus j)
    (x j - center j) heta (hm j hj) (hp j hj) (hx.2 j hj)

/-- Every separation theorem for coordinate enclosures transfers to actual
asymmetric coordinate tubes. `hsep` is normally one of the derived theorems
above; it is not a geometric axiom of the native construction. -/
theorem asymmetricCoordinateTube_disjoint_of_coordinateTube_disjoint
    (i j : ι) (c c' : ι → ℝ) (pMinus pPlus pMinus' pPlus' : ι → ℝ)
    (eta rho : ℝ) (heta : 0 ≤ eta)
    (hm : ∀ k, k ≠ i → 1 ≤ pMinus k) (hp : ∀ k, k ≠ i → 1 ≤ pPlus k)
    (hm' : ∀ k, k ≠ j → 1 ≤ pMinus' k) (hp' : ∀ k, k ≠ j → 1 ≤ pPlus' k)
    (hsep : Disjoint (coordinateTube i c eta rho) (coordinateTube j c' eta rho)) :
    Disjoint (asymmetricCoordinateTube i c pMinus pPlus eta rho)
      (asymmetricCoordinateTube j c' pMinus' pPlus' eta rho) :=
  hsep.mono (asymmetricCoordinateTube_subset_coordinateTube i c pMinus pPlus eta rho heta hm hp)
    (asymmetricCoordinateTube_subset_coordinateTube j c' pMinus' pPlus' eta rho heta hm' hp')

#print axioms native_tangent_distance_from_integer
#print axioms native_coordinateTube_disjoint_of_different_normals
#print axioms native_coordinateTube_disjoint_of_distinct_integer_planes
#print axioms native_coordinateTube_disjoint_of_distinct_orbit_coordinates
#print axioms native_coordinateTube_disjoint_of_distinct_tangent_cells
#print axioms asymmetricCoordinateTube_subset_coordinateTube
end PhysicalRegistration
