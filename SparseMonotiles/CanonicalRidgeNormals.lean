module

public import SparseMonotiles.ReferenceKeyHalfspaces
public import SparseMonotiles.PyramidIncidence
public import SparseMonotiles.KeyAngles

@[expose] public section

/-!
# Active ridge pairs and their exact Euclidean normal angles

The listed facet equations are those of the actual convex-hull keys. Away
from the apex, every pair of distinct active equations is either base--side
or side--side on distinct tangential axes. The redundant upper-height
inequality is not a facet and is inactive there.

The angle formulas below concern Euclidean normals, with the base normal
reversed when measuring its acute crease deviation. They do not themselves
assert that a transverse section of the full bumped/dented tile is a wedge,
nor that no other key or carrier piece meets a given section.
-/
namespace SparseMonotiles

/-- The two possible kinds of distinct active facet pairs below the apex. -/
def IsPyramidRidgePair {n : ℕ} (a b : PyramidFacetIndex n) : Prop :=
  match a, b with
  | none, some _ => True
  | some _, none => True
  | some (i, _), some (j, _) => i ≠ j
  | none, none => False

/-- Complete pair classification; it does not assume that only two facets are active. -/
theorem active_pyramidFacet_pair_classification {n : ℕ}
    (lo hi o : Fin n → ℝ) {h : ℝ} {p : PyramidPoint n}
    (hwidth : ∀ i, lo i < hi i) (hph : p.2 < h)
    {a b : PyramidFacetIndex n}
    (ha : p ∈ pyramidFacetPlane lo hi o h a)
    (hb : p ∈ pyramidFacetPlane lo hi o h b) (hab : a ≠ b) :
    IsPyramidRidgePair a b := by
  have hc : pyramidFacetCoordinate a ≠ pyramidFacetCoordinate b := by
    intro heq
    apply hab
    exact pyramidFacetCoordinate_injOn_active_below_apex lo hi o hwidth hph
      ((mem_pyramidActiveFacets lo hi o h p a).mpr ha)
      ((mem_pyramidActiveFacets lo hi o h p b).mpr hb) heq
  cases a with
  | none =>
      cases b with
      | none => exact False.elim (hab rfl)
      | some s => trivial
  | some s =>
      cases b with
      | none => trivial
      | some t =>
          rcases s with ⟨i, u⟩
          rcases t with ⟨j, v⟩
          simpa [IsPyramidRidgePair, pyramidFacetCoordinate] using hc

/-- A member of the actual key other than its apex has strictly smaller height. -/
theorem key_height_lt_of_ne_apex {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) {x : Point (n + 1)}
    (hx : x ∈ keySolid k) (hne : x ≠ rationalPoint k.apex) :
    x (Fin.last n) < keyPyramidHeight k := by
  have hp := (mem_keySolid_iff_pyramidHalfspaces k hc hr hh x).mp hx
  apply lt_of_le_of_ne hp.2.1
  intro heq
  have hp' := eq_apex_of_mem_pyramidHalfspaces_of_height_eq
    (keyPyramidLo k) (keyPyramidHi k) (keyPyramidApex k) hh hp heq
  apply hne
  apply (pointPyramidEquiv n).injective
  exact hp'

/-- Every active H-representation equation away from the apex is a genuine facet. -/
theorem active_key_halfspace_is_facet {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) {x : Point (n + 1)}
    (hx : x ∈ keySolid k) (hne : x ≠ rationalPoint k.apex)
    (j : PyramidHalfspaceIndex n) (hj : keyPyramidHalfspaceSlack k j x = 0) :
    ∃ a : PyramidFacetIndex n, pyramidFacetHalfspaceIndex a = j ∧
      pointPyramidEquiv n x ∈ pyramidFacetPlane (keyPyramidLo k)
        (keyPyramidHi k) (keyPyramidApex k) (keyPyramidHeight k) a := by
  have heq : keyPyramidHalfspaceNormal k j x = keyPyramidHalfspaceBound k j :=
    sub_eq_zero.mp hj |>.symm
  have hfacet (a : PyramidFacetIndex n) (ha : pyramidFacetHalfspaceIndex a = j) :
      pointPyramidEquiv n x ∈ pyramidFacetPlane (keyPyramidLo k)
        (keyPyramidHi k) (keyPyramidApex k) (keyPyramidHeight k) a := by
    rw [mem_pyramidFacetPlane_iff, ha]
    exact heq
  rcases j with b | s
  · cases b
    · exact ⟨none, rfl, hfacet none rfl⟩
    · have hlt := key_height_lt_of_ne_apex k hc hr hh hx hne
      change x (Fin.last n) = keyPyramidHeight k at heq
      exact False.elim (hlt.ne heq)
  · exact ⟨some s, rfl, hfacet (some s) rfl⟩

/-- Distinct active planes of the actual key have exactly the advertised pair types. -/
theorem active_key_halfspace_pair_classification {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hwidth : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    {x : Point (n + 1)} (hx : x ∈ keySolid k) (hne : x ≠ rationalPoint k.apex)
    {j l : PyramidHalfspaceIndex n} (hjl : j ≠ l)
    (hj : keyPyramidHalfspaceSlack k j x = 0)
    (hl : keyPyramidHalfspaceSlack k l x = 0) :
    ∃ a b : PyramidFacetIndex n,
      pyramidFacetHalfspaceIndex a = j ∧ pyramidFacetHalfspaceIndex b = l ∧
      IsPyramidRidgePair a b := by
  obtain ⟨a, ha, hxa⟩ := active_key_halfspace_is_facet k hc hr hh hx hne j hj
  obtain ⟨b, hb, hxb⟩ := active_key_halfspace_is_facet k hc hr hh hx hne l hl
  refine ⟨a, b, ha, hb, active_pyramidFacet_pair_classification
    (keyPyramidLo k) (keyPyramidHi k) (keyPyramidApex k) hwidth
    (key_height_lt_of_ne_apex k hc hr hh hx hne) hxa hxb ?_⟩
  intro hab
  apply hjl
  rw [← ha, ← hb, hab]

/-- Outward base normal. -/
noncomputable def pyramidBaseNormal (n : ℕ) : Point (n + 1) :=
  EuclideanSpace.single (Fin.last n) (-1)

/-- A side's outward normal rescaled so its last coordinate is one. -/
noncomputable def pyramidSlopeNormal {n : ℕ} (i : Fin n) (b : Bool) (s : ℝ) :
    Point (n + 1) :=
  EuclideanSpace.single (Fin.last n) 1 +
    EuclideanSpace.single i.castSucc (if b then s else -s)

@[simp] theorem inner_pyramidBaseNormal {n : ℕ} (x : Point (n + 1)) :
    inner (𝕜 := ℝ) (pyramidBaseNormal n) x = -x (Fin.last n) := by
  simp [pyramidBaseNormal, EuclideanSpace.inner_single_left]

@[simp] theorem inner_pyramidSlopeNormal {n : ℕ} (i : Fin n) (b : Bool)
    (s : ℝ) (x : Point (n + 1)) :
    inner (𝕜 := ℝ) (pyramidSlopeNormal i b s) x =
      x (Fin.last n) + (if b then s else -s) * x i.castSucc := by
  cases b <;> simp [pyramidSlopeNormal, inner_add_left, EuclideanSpace.inner_single_left, mul_comm]

@[simp] theorem pyramidSlopeNormal_last {n : ℕ} (i : Fin n) (b : Bool) (s : ℝ) :
    pyramidSlopeNormal i b s (Fin.last n) = 1 := by
  simp [pyramidSlopeNormal, EuclideanSpace.single_apply, Ne.symm (Fin.castSucc_ne_last i)]

@[simp] theorem pyramidSlopeNormal_same {n : ℕ} (i : Fin n) (b : Bool) (s : ℝ) :
    pyramidSlopeNormal i b s i.castSucc = if b then s else -s := by
  simp [pyramidSlopeNormal, EuclideanSpace.single_apply]

@[simp] theorem pyramidSlopeNormal_other {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (b : Bool) (s : ℝ) : pyramidSlopeNormal j b s i.castSucc = 0 := by
  simp [pyramidSlopeNormal, EuclideanSpace.single_apply, hij]

@[simp] theorem pyramidBaseNormal_norm (n : ℕ) : ‖pyramidBaseNormal n‖ = 1 := by
  simp [pyramidBaseNormal]

@[simp] theorem pyramidSlopeNormal_norm_sq {n : ℕ} (i : Fin n) (b : Bool) (s : ℝ) :
    ‖pyramidSlopeNormal i b s‖ ^ 2 = 1 + s ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_pyramidSlopeNormal,
    pyramidSlopeNormal_last, pyramidSlopeNormal_same]
  cases b <;> simp [sq]

@[simp] theorem pyramidSlopeNormal_norm {n : ℕ} (i : Fin n) (b : Bool) (s : ℝ) :
    ‖pyramidSlopeNormal i b s‖ = Real.sqrt (1 + s ^ 2) := by
  rw [← pyramidSlopeNormal_norm_sq i b s, Real.sqrt_sq (norm_nonneg _)]

@[simp] theorem inner_pyramidBaseNormal_slope {n : ℕ} (i : Fin n) (b : Bool) (s : ℝ) :
    inner (𝕜 := ℝ) (pyramidBaseNormal n) (pyramidSlopeNormal i b s) = -1 := by
  rw [inner_pyramidBaseNormal, pyramidSlopeNormal_last]

/-- Orthogonal tangential axes leave only the product of last coordinates. -/
theorem inner_pyramidSlopeNormal_distinct {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (b c : Bool) (s t : ℝ) :
    inner (𝕜 := ℝ) (pyramidSlopeNormal i b s) (pyramidSlopeNormal j c t) = 1 := by
  rw [inner_pyramidSlopeNormal, pyramidSlopeNormal_last, pyramidSlopeNormal_other i j hij]
  simp only [mul_zero, add_zero]

/-- The apex-to-endpoint distance used for a positive normal rescaling. -/
noncomputable def keySideDistance {n : ℕ} (k : KeyData (n + 1)) (i : Fin n)
    (b : Bool) : ℝ :=
  if b then keyPyramidHi k i - keyPyramidApex k i
  else keyPyramidApex k i - keyPyramidLo k i

noncomputable def keySideSlope {n : ℕ} (k : KeyData (n + 1)) (i : Fin n)
    (b : Bool) : ℝ := keyPyramidHeight k / keySideDistance k i b

/-- The computed vector is a positive multiple of the actual outward side form. -/
theorem key_side_form_eq_distance_mul_inner {n : ℕ} (k : KeyData (n + 1))
    (i : Fin n) (b : Bool) (hd : 0 < keySideDistance k i b) (x : Point (n + 1)) :
    keyPyramidHalfspaceNormal k (.inr (i, b)) x =
      keySideDistance k i b *
        inner (𝕜 := ℝ) (pyramidSlopeNormal i b (keySideSlope k i b)) x := by
  rw [keyPyramidHalfspaceNormal_apply, inner_pyramidSlopeNormal]
  have hne := ne_of_gt hd
  cases b <;> simp only [keySideDistance, keySideSlope, Bool.false_eq_true, ↓reduceIte] at *
  · field_simp
    <;> ring
  · field_simp
    <;> ring

/-- Cosine of the acute deviation between the reversed base normal and a side normal. -/
theorem base_slope_normal_cosine {n : ℕ} (i : Fin n) (b : Bool) (s : ℝ) :
    -inner (𝕜 := ℝ) (pyramidBaseNormal n) (pyramidSlopeNormal i b s) /
      (‖pyramidBaseNormal n‖ * ‖pyramidSlopeNormal i b s‖) =
      1 / Real.sqrt (1 + s ^ 2) := by
  rw [inner_pyramidBaseNormal_slope, pyramidBaseNormal_norm, pyramidSlopeNormal_norm]
  simp only [neg_neg, one_mul]

/-- Exact cosine of the angle between two distinct-axis side normals. -/
theorem distinct_slope_normal_cosine {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (b c : Bool) (s t : ℝ) :
    inner (𝕜 := ℝ) (pyramidSlopeNormal i b s) (pyramidSlopeNormal j c t) /
      (‖pyramidSlopeNormal i b s‖ * ‖pyramidSlopeNormal j c t‖) =
      1 / Real.sqrt ((1 + s ^ 2) * (1 + t ^ 2)) := by
  rw [inner_pyramidSlopeNormal_distinct i j hij,
    pyramidSlopeNormal_norm, pyramidSlopeNormal_norm,
    Real.sqrt_mul (by positivity : 0 ≤ 1 + s ^ 2)]

/-- The base-normal formula realizes precisely the previously bounded arctangent. -/
theorem base_slope_normal_deviation {n : ℕ} (i : Fin n) (b : Bool) (s : ℝ)
    (hs : 0 ≤ s) :
    Real.arccos (-inner (𝕜 := ℝ) (pyramidBaseNormal n) (pyramidSlopeNormal i b s) /
      (‖pyramidBaseNormal n‖ * ‖pyramidSlopeNormal i b s‖)) = baseCreaseDeviation s := by
  rw [base_slope_normal_cosine, ← Real.cos_arctan]
  apply Real.arccos_cos
  · simpa using (Real.arctan_le_arctan_iff.mpr hs)
  · linarith [Real.arctan_lt_pi_div_two s, Real.pi_pos]

/-- The distinct-axis formula realizes precisely the previously bounded arccosine. -/
theorem distinct_slope_normal_deviation {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (b c : Bool) (s t : ℝ) :
    Real.arccos (inner (𝕜 := ℝ) (pyramidSlopeNormal i b s) (pyramidSlopeNormal j c t) /
      (‖pyramidSlopeNormal i b s‖ * ‖pyramidSlopeNormal j c t‖)) =
      sideCreaseDeviation s t := by
  rw [distinct_slope_normal_cosine i j hij]
  rfl

namespace Canonical

noncomputable def referenceSideSlope5 (i : Fin 4) (b : Bool) : ℝ :=
  keySideSlope ((referenceBox5 true).toKeyData 19200) i b

noncomputable def referenceSideSlope7 (i : Fin 6) (b : Bool) : ℝ :=
  keySideSlope ((referenceBox7 true).toKeyData 188160) i b

/-- These are the slopes of the literal checked five-dimensional key. -/
theorem referenceSideSlope5_bounds (i : Fin 4) (b : Bool) :
    0 < referenceSideSlope5 i b ∧ referenceSideSlope5 i b ≤ 1/2 := by
  fin_cases i <;> cases b <;>
    norm_num [referenceSideSlope5, keySideSlope, keySideDistance,
      keyPyramidHeight, keyPyramidHi, keyPyramidLo, keyPyramidApex,
      referenceBox5, Contact.BoxKey.toKeyData, Contact.rationalVertex, Fin.last]

/-- These are the slopes of the literal checked seven-dimensional key. -/
theorem referenceSideSlope7_bounds (i : Fin 6) (b : Bool) :
    0 < referenceSideSlope7 i b ∧ referenceSideSlope7 i b ≤ 1/2 := by
  fin_cases i <;> cases b <;>
    norm_num [referenceSideSlope7, keySideSlope, keySideDistance,
      keyPyramidHeight, keyPyramidHi, keyPyramidLo, keyPyramidApex,
      referenceBox7, Contact.BoxKey.toKeyData, Contact.rationalVertex, Fin.last]

/-- The rescaling to the actual facet forms is positive, not merely nonzero. -/
theorem referenceSideDistance5_pos (i : Fin 4) (b : Bool) :
    0 < keySideDistance ((referenceBox5 true).toKeyData 19200) i b := by
  fin_cases i <;> cases b <;>
    norm_num [keySideDistance, keyPyramidHi, keyPyramidLo, keyPyramidApex,
      referenceBox5, Contact.BoxKey.toKeyData, Contact.rationalVertex, Fin.last]

theorem referenceSideDistance7_pos (i : Fin 6) (b : Bool) :
    0 < keySideDistance ((referenceBox7 true).toKeyData 188160) i b := by
  fin_cases i <;> cases b <;>
    norm_num [keySideDistance, keyPyramidHi, keyPyramidLo, keyPyramidApex,
      referenceBox7, Contact.BoxKey.toKeyData, Contact.rationalVertex, Fin.last]

end Canonical

#print axioms active_key_halfspace_pair_classification
#print axioms key_side_form_eq_distance_mul_inner
#print axioms base_slope_normal_deviation
#print axioms distinct_slope_normal_deviation

end SparseMonotiles
