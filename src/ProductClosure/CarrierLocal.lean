module

public import ProductClosure.Polycube

@[expose] public section

namespace ProductClosure.Polycube
open Set
open scoped InnerProductSpace
noncomputable section

/-- An open box about the unit facet center, wholly inside its tangential
relative interior. -/
def facetNeighborhood {d : ℕ} {S : Finset (LatticeIndex d)} (f : Facet S) : Set (Space d) :=
  {x | ∀ k, |x k - facetCenter f k| < 1 / 2}

theorem facetNeighborhood_isOpen {d : ℕ} {S : Finset (LatticeIndex d)}
    (f : Facet S) : IsOpen (facetNeighborhood f) := by
  have h : facetNeighborhood f = ⋂ k, {x : Space d | |x k - facetCenter f k| < 1 / 2} := by
    ext x; simp [facetNeighborhood]
  rw [h]
  apply isOpen_iInter_of_finite
  intro k
  exact isOpen_lt (((EuclideanSpace.proj k).continuous.sub continuous_const).abs) continuous_const

/-- An interior point of a unit interval identifies its integer cell. -/
theorem integer_cell_unique (b n : ℤ) (x : ℝ)
    (hb : (b : ℝ) < x ∧ x < (b : ℝ) + 1)
    (hn : (n : ℝ) ≤ x ∧ x ≤ (n : ℝ) + 1) : n = b := by
  have h₁ : (b : ℝ) < (n : ℝ) + 1 := hb.1.trans_le hn.2
  have h₂ : (n : ℝ) < (b : ℝ) + 1 := hn.1.trans_lt hb.2
  have h₁' : b < n + 1 := by exact_mod_cast h₁
  have h₂' : n < b + 1 := by exact_mod_cast h₂
  omega

theorem facetNeighborhood_tangent {d : ℕ} {S : Finset (LatticeIndex d)}
    (f : Facet S) {x : Space d} (hx : x ∈ facetNeighborhood f)
    (k : Fin d) (hk : k ≠ f.axis) :
    (f.cell.val k : ℝ) < x k ∧ x k < (f.cell.val k : ℝ) + 1 := by
  have h := abs_lt.mp (hx k)
  rw [facetCenter_tangent f k hk] at h
  constructor <;> linarith

/-- Outside the exposed halfspace, the only possible lattice cell is the
specified missing neighbor. This derives the chart from finite occupancy. -/
theorem mem_carrier_local_side {d : ℕ} {S : Finset (LatticeIndex d)}
    (f : Facet S) (x : Space d) (hx : x ∈ facetNeighborhood f) :
    x ∈ carrier S ↔ if f.positive then x f.axis ≤ (f.cell.val f.axis : ℝ) + 1
      else (f.cell.val f.axis : ℝ) ≤ x f.axis := by
  have hn := abs_lt.mp (hx f.axis)
  rw [facetCenter_normal] at hn
  constructor
  · intro hmem
    obtain ⟨w, hw, hxw⟩ := (mem_carrier_iff S x).mp hmem
    by_contra hout
    have heq : w = facetOutsideIndex f := by
      funext k
      by_cases hk : k = f.axis
      · subst k
        apply integer_cell_unique _ _ _ ?_ (hxw f.axis)
        cases hp : f.positive <;>
          simp [facetOutsideIndex, latticeStep, facetPlane, hp] at hn hout ⊢ <;>
          constructor <;> linarith
      · have he := integer_cell_unique _ _ _ (facetNeighborhood_tangent f hx k hk) (hxw k)
        simpa [facetOutsideIndex, latticeStep, hk] using he
    apply f.outside
    change facetOutsideIndex f ∈ S
    rwa [← heq]
  · intro hside
    apply (mem_carrier_iff S x).mpr
    refine ⟨f.cell.val, f.cell.property, fun k => ?_⟩
    by_cases hk : k = f.axis
    · subst k
      cases hp : f.positive <;> simp [facetPlane, hp] at hn hside <;>
        constructor <;> linarith
    · have ht := facetNeighborhood_tangent f hx k hk
      exact ⟨ht.1.le, ht.2.le⟩

theorem outward_inner_coordinate {d : ℕ} {S : Finset (LatticeIndex d)}
    (f : Facet S) (v : Space d) :
    ⟪outward f, v⟫_ℝ = sign f.positive * v f.axis := by
  simp [outward, real_inner_smul_left, EuclideanSpace.inner_single_left]

/-- Every exposed facet of every finite polycube has its actual local
halfspace chart, including carriers with holes or reentrant corners. -/
theorem mem_carrier_local_halfspace {d : ℕ} {S : Finset (LatticeIndex d)}
    (f : Facet S) (x : Space d) (hx : x ∈ facetNeighborhood f) :
    x ∈ carrier S ↔ ⟪outward f, x - facetCenter f⟫_ℝ ≤ 0 := by
  rw [mem_carrier_local_side f x hx, outward_inner_coordinate]
  simp only [PiLp.sub_apply, facetCenter_normal]
  cases hp : f.positive <;> simp [hp, sign, facetPlane] <;> linarith

/-- Two exposed facets on the same geometric unit facet cannot point in
opposite directions: that would make an occupied cell a missing neighbor. -/
theorem facet_positive_eq_of_coordinates {d : ℕ} {S : Finset (LatticeIndex d)}
    (f g : Facet S) (ha : f.axis = g.axis) (hp : facetPlane f = facetPlane g)
    (ht : ∀ k, k ≠ f.axis → f.cell.val k = g.cell.val k) :
    f.positive = g.positive := by
  by_contra hpos
  have heq : facetOutsideIndex f = g.cell.val := by
    funext k
    by_cases hk : k = f.axis
    · subst k
      have hplane := hp
      rw [facetPlane, facetPlane, ← ha] at hplane
      cases hf : f.positive <;> cases hg : g.positive <;>
        simp [hf, hg] at hpos hplane ⊢ <;>
        simp [facetOutsideIndex, latticeStep, hf] <;> omega
    · simpa [facetOutsideIndex, latticeStep, hk] using ht k hk
  apply f.outside
  change facetOutsideIndex f ∈ S
  rw [heq]
  exact g.cell.property

/-- Geometric extensionality for exposed facets, derived from occupancy. -/
theorem facet_eq_of_coordinates {d : ℕ} {S : Finset (LatticeIndex d)}
    (f g : Facet S) (ha : f.axis = g.axis) (hp : facetPlane f = facetPlane g)
    (ht : ∀ k, k ≠ f.axis → f.cell.val k = g.cell.val k) : f = g := by
  have hpos := facet_positive_eq_of_coordinates f g ha hp ht
  have hc : f.cell = g.cell := by
    apply Subtype.ext
    funext k
    by_cases hk : k = f.axis
    · subst k
      have hplane := hp
      simp only [facetPlane, ← ha, ← hpos] at hplane
      omega
    · exact ht k hk
  cases f; cases g
  simp_all

end
end ProductClosure.Polycube
