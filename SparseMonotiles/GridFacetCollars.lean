module

public import SparseMonotiles.Model

@[expose] public section

/-!
# Disjoint closed collars of unoriented integer unit facets

A facet is identified by its axis and its integer anchor, not by an outward normal.
The axis coordinate of the anchor is the level of the supporting plane; the other
coordinates are the lower corners of the tangential unit intervals. Thus the two
possible normal orientations of the same geometric facet have one identifier.

The closed collar has normal half-width `1/8` and tangential half-width `1/4`
about the facet centre. Distinct identifiers have disjoint collars, including
when their axes differ. No positive-dimension hypothesis is needed: `GridFacet 0`
is empty because its `axis` field would belong to `Fin 0`.
-/

namespace SparseMonotiles

/-- An unoriented unit facet in the integer grid. -/
structure GridFacet (d : ℕ) where
  axis : Fin d
  anchor : Fin d → ℤ
  deriving DecidableEq

@[ext] theorem GridFacet.ext {d : ℕ} {f g : GridFacet d}
    (haxis : f.axis = g.axis) (hanchor : f.anchor = g.anchor) : f = g := by
  cases f
  cases g
  cases haxis
  cases hanchor
  rfl

/-- A central, closed collar, with no orientation field or orientation choice. -/
def gridFacetCollar {d : ℕ} (f : GridFacet d) : Set (Point d) :=
  {x | |x f.axis - (f.anchor f.axis : ℝ)| ≤ 1 / 8 ∧
    ∀ i, i ≠ f.axis → |x i - ((f.anchor i : ℝ) + 1 / 2)| ≤ 1 / 4}

@[simp] theorem mem_gridFacetCollar {d : ℕ} (f : GridFacet d) (x : Point d) :
    x ∈ gridFacetCollar f ↔
      |x f.axis - (f.anchor f.axis : ℝ)| ≤ 1 / 8 ∧
      ∀ i, i ≠ f.axis → |x i - ((f.anchor i : ℝ) + 1 / 2)| ≤ 1 / 4 := Iff.rfl

/-- Integers less than one apart are equal. -/
theorem gridFacet_int_eq_of_abs_sub_lt_one {m n : ℤ}
    (h : |(m : ℝ) - (n : ℝ)| < 1) : m = n := by
  have hlo : (-1 : ℤ) < m - n := by exact_mod_cast (abs_lt.mp h).1
  have hhi : m - n < (1 : ℤ) := by exact_mod_cast (abs_lt.mp h).2
  omega

/-- An integer and a half-integer are at least one half apart. -/
theorem gridFacet_int_halfInt_gap (m n : ℤ) :
    (1 / 2 : ℝ) ≤ |(m : ℝ) - ((n : ℝ) + 1 / 2)| := by
  by_cases hmn : m ≤ n
  · have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have ha := neg_le_abs ((m : ℝ) - ((n : ℝ) + 1 / 2))
    linarith
  · have hnm : n + 1 ≤ m := by omega
    have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnm
    have ha := le_abs_self ((m : ℝ) - ((n : ℝ) + 1 / 2))
    linarith

private theorem gridFacet_int_eq_of_common_shifted_near {m n : ℤ}
    {x shift r s : ℝ}
    (hm : |x - ((m : ℝ) + shift)| ≤ r)
    (hn : |x - ((n : ℝ) + shift)| ≤ s) (hrs : r + s < 1) : m = n := by
  apply gridFacet_int_eq_of_abs_sub_lt_one
  rcases abs_le.mp hm with ⟨hml, hmu⟩
  rcases abs_le.mp hn with ⟨hnl, hnu⟩
  apply abs_lt.mpr
  constructor <;> linarith

/-- The normal strip of one axis misses the tangential strip of another axis. -/
theorem gridFacet_normal_tangent_incompatible {m n : ℤ} {x : ℝ}
    (hnormal : |x - (m : ℝ)| ≤ 1 / 8)
    (htangent : |x - ((n : ℝ) + 1 / 2)| ≤ 1 / 4) : False := by
  rcases abs_le.mp hnormal with ⟨hnl, hnu⟩
  rcases abs_le.mp htangent with ⟨htl, htu⟩
  have hlo : (n : ℝ) < (m : ℝ) := by linarith
  have hhi : (m : ℝ) < (n : ℝ) + 1 := by linarith
  have hlo' : n < m := by exact_mod_cast hlo
  have hhi' : m < n + 1 := by exact_mod_cast hhi
  omega

/-- A point in two closed collars forces equality of both the axis and the anchor. -/
theorem GridFacet.eq_of_mem_collars {d : ℕ} {f g : GridFacet d} {x : Point d}
    (hf : x ∈ gridFacetCollar f) (hg : x ∈ gridFacetCollar g) : f = g := by
  have haxis : f.axis = g.axis := by
    by_contra hne
    exact gridFacet_normal_tangent_incompatible hf.1 (hg.2 f.axis hne)
  apply GridFacet.ext haxis
  funext i
  by_cases hi : i = f.axis
  · subst i
    have hg' : |x f.axis - (g.anchor f.axis : ℝ)| ≤ 1 / 8 := by
      have hxaxis : x f.axis = x g.axis := congrArg x haxis
      have haaxis : g.anchor f.axis = g.anchor g.axis := congrArg g.anchor haxis
      rw [hxaxis, haaxis]
      exact hg.1
    apply gridFacet_int_eq_of_common_shifted_near (shift := 0)
      (r := 1 / 8) (s := 1 / 8)
    · simpa only [add_zero] using hf.1
    · simpa only [add_zero] using hg'
    · norm_num
  · exact gridFacet_int_eq_of_common_shifted_near
      (hf.2 i hi) (hg.2 i (by simpa only [haxis] using hi)) (by norm_num)

/-- Distinct unoriented integer unit facets have disjoint closed collars. -/
theorem gridFacetCollars_disjoint {d : ℕ} {f g : GridFacet d} (hfg : f ≠ g) :
    Disjoint (gridFacetCollar f) (gridFacetCollar g) := by
  apply Set.disjoint_left.mpr
  intro x hf hg
  exact hfg (GridFacet.eq_of_mem_collars hf hg)

/-- The full grid family is pairwise disjoint, without a finiteness restriction. -/
theorem gridFacetCollars_pairwiseDisjoint (d : ℕ) :
    Pairwise (fun f g : GridFacet d => Disjoint (gridFacetCollar f) (gridFacetCollar g)) := by
  intro f g hfg
  exact gridFacetCollars_disjoint hfg

/-- Any geometric objects contained in distinct facet collars are disjoint. -/
theorem disjoint_of_subset_gridFacetCollars {d : ℕ} {f g : GridFacet d}
    {A B : Set (Point d)} (hfg : f ≠ g)
    (hA : A ⊆ gridFacetCollar f) (hB : B ⊆ gridFacetCollar g) : Disjoint A B :=
  (gridFacetCollars_disjoint hfg).mono hA hB

/-- A collar misses a union of objects carried by other facets.
This applies in particular to finite key families. -/
theorem gridFacetCollar_disjoint_iUnion {d : ℕ} {ι : Type*}
    (facets : ι → GridFacet d) (A : ι → Set (Point d)) {f : GridFacet d}
    (hne : ∀ i, f ≠ facets i) (hA : ∀ i, A i ⊆ gridFacetCollar (facets i)) :
    Disjoint (gridFacetCollar f) (⋃ i, A i) := by
  apply Set.disjoint_iUnion_right.mpr
  intro i
  exact (gridFacetCollars_disjoint (hne i)).mono_right (hA i)

/-- Each collar is closed in the Euclidean topology. -/
theorem gridFacetCollar_isClosed {d : ℕ} (f : GridFacet d) :
    IsClosed (gridFacetCollar f) := by
  have hcoord (i : Fin d) : Continuous (fun x : Point d => x i) :=
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  have hnormal : IsClosed {x : Point d |
      |x f.axis - (f.anchor f.axis : ℝ)| ≤ 1 / 8} :=
    isClosed_le (((hcoord f.axis).sub continuous_const).abs) continuous_const
  have htangent : ∀ i : Fin d, IsClosed {x : Point d |
      |x i - ((f.anchor i : ℝ) + 1 / 2)| ≤ 1 / 4} := by
    intro i
    exact isClosed_le (((hcoord i).sub continuous_const).abs) continuous_const
  have hset : gridFacetCollar f =
      {x : Point d | |x f.axis - (f.anchor f.axis : ℝ)| ≤ 1 / 8} ∩
      ⋂ i : Fin d, ⋂ (_ : i ≠ f.axis), {x : Point d |
        |x i - ((f.anchor i : ℝ) + 1 / 2)| ≤ 1 / 4} := by
    ext x
    simp only [gridFacetCollar, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  exact hnormal.inter (isClosed_iInter fun i => isClosed_iInter fun _ => htangent i)

#print axioms GridFacet.eq_of_mem_collars
#print axioms gridFacetCollars_disjoint
#print axioms gridFacetCollars_pairwiseDisjoint
#print axioms disjoint_of_subset_gridFacetCollars
#print axioms gridFacetCollar_disjoint_iUnion
#print axioms gridFacetCollar_isClosed

end SparseMonotiles
