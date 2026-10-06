module

public import SparseMonotiles.CarrierFacetHalfspace
public import SparseMonotiles.KeyCovariance

@[expose] public section

/-!
Registered signed-integer poses act on actual oriented unit facets and their
closed collars. A coincident nonempty pair of collar-contained solids determines
the same unoriented facet; distinct owner cells force opposed normals. There is
no assumption that an arbitrary physical placement is registered.
-/
namespace SparseMonotiles.Contact

/-- Transport an oriented unit facet. The lower-cell correction is inherited
from `Pose.cell`; the outward flag changes under a negative normal row. -/
def Pose.facet {d : ℕ} (p : Pose d) (f : Facet d) : Facet d where
  cell := p.cell f.cell
  axis := p.perm.symm f.axis
  positive := if p.negative (p.perm.symm f.axis) then !f.positive else f.positive

@[simp] theorem Pose.facet_axis_iff {d : ℕ} (p : Pose d) (f : Facet d) (i : Fin d) :
    i = (p.facet f).axis ↔ p.perm i = f.axis := by
  change i = p.perm.symm f.axis ↔ p.perm i = f.axis
  exact p.perm.eq_symm_apply

@[simp] theorem Pose.facet_normal {d : ℕ} (p : Pose d) (f : Facet d) :
    (p.facet f).normal = p.sign (p.facet f).axis * f.normal := by
  cases hn : p.negative (p.perm.symm f.axis) <;> cases hf : f.positive <;>
    simp [Pose.facet, Facet.normal, Pose.sign, hn, hf]

@[simp] theorem Pose.facet_centre2 {d : ℕ} (p : Pose d) (f : Facet d) :
    (p.facet f).centre2 = p.scaledPoint 2 f.centre2 := by
  funext i
  have hai := p.facet_axis_iff f i
  by_cases hi : i = (p.facet f).axis
  · have hpi := hai.mp hi
    simp only [Facet.centre2, if_pos hi, if_pos hpi, Pose.facet_normal,
      Pose.scaledPoint]
    change 2 * p.cell f.cell i + 1 + p.sign (p.facet f).axis * f.normal = _
    rw [← hi]
    cases hn : p.negative i <;> simp [Pose.cell, Pose.sign, hn] <;> ring
  · have hpi : p.perm i ≠ f.axis := fun h => hi (hai.mpr h)
    simp only [Facet.centre2, if_neg hi, if_neg hpi, add_zero, Pose.scaledPoint]
    change 2 * p.cell f.cell i + 1 = _
    cases hn : p.negative i <;> simp [Pose.cell, Pose.sign, hn] <;> ring

/-- The oriented doubled centre depends only on the unoriented grid facet. -/
theorem Facet.centre2_eq_grid {d : ℕ} (f : Facet d) (i : Fin d) :
    f.centre2 i = 2 * f.gridFacet.anchor i + if i = f.axis then 0 else 1 := by
  by_cases hi : i = f.axis <;> cases hp : f.positive <;>
    simp [Facet.centre2, Facet.gridFacet, Facet.normal, hi, hp] <;> ring

theorem Facet.centre2_eq_of_gridFacet_eq {d : ℕ} {f g : Facet d}
    (h : f.gridFacet = g.gridFacet) : f.centre2 = g.centre2 := by
  have ha : f.axis = g.axis := congrArg GridFacet.axis h
  funext i
  rw [f.centre2_eq_grid i, g.centre2_eq_grid i, ha, h]

/-- Uniform coordinate form of the genuine closed facet collar. -/
theorem Facet.mem_collar_iff_centre2 {d : ℕ} (f : Facet d) (x : Point d) :
    x ∈ gridFacetCollar f.gridFacet ↔
      ∀ i, |x i - (f.centre2 i : ℝ) / 2| ≤ if i = f.axis then 1/8 else 1/4 := by
  have hc (i : Fin d) : (f.centre2 i : ℝ) / 2 =
      (f.gridFacet.anchor i : ℝ) + if i = f.axis then 0 else 1/2 := by
    rw [f.centre2_eq_grid i]
    split_ifs <;> push_cast <;> ring
  constructor
  · intro hx i
    rw [hc i]
    by_cases hi : i = f.axis
    · subst i
      simpa using hx.1
    · simpa [hi] using hx.2 i hi
  · intro hx
    constructor
    · simpa [hc] using hx f.axis
    · intro i hi
      change i ≠ f.axis at hi
      simpa [hc, hi] using hx i

/-- Closed collars are covariant under the actual affine isometry. -/
theorem Pose.mapsTo_facet_collar {d : ℕ} (p : Pose d) (f : Facet d) :
    Set.MapsTo p.euclidean (gridFacetCollar f.gridFacet)
      (gridFacetCollar (p.facet f).gridFacet) := by
  intro x hx
  apply ((p.facet f).mem_collar_iff_centre2 (p.euclidean x)).mpr
  have hx' := (f.mem_collar_iff_centre2 x).mp hx
  intro i
  have hdisp : p.euclidean x i - ((p.facet f).centre2 i : ℝ)/2 =
      (p.sign i : ℝ) * (x (p.perm i) - (f.centre2 (p.perm i) : ℝ)/2) := by
    rw [p.euclidean_apply, p.facet_centre2]
    simp only [Pose.scaledPoint, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    ring
  rw [hdisp]
  have habs (u : ℝ) : |(p.sign i : ℝ) * u| = |u| := by
    cases hn : p.negative i <;> simp [Pose.sign, hn]
  rw [habs]
  simpa only [p.facet_axis_iff f i] using hx' (p.perm i)

/-- With unequal owner cells, two oriented copies of one geometric facet must
have opposite normals. This does not require chair-specific exposure. -/
theorem Facet.normal_opposite_of_gridFacet_eq {d : ℕ} {a b : Facet d}
    (hgrid : a.gridFacet = b.gridFacet) (hcell : a.cell ≠ b.cell) :
    b.normal = -a.normal := by
  have ha : a.axis = b.axis := congrArg GridFacet.axis hgrid
  have hp : a.positive ≠ b.positive := by
    intro hp
    apply hcell
    funext i
    have hi := congrFun (congrArg GridFacet.anchor hgrid) i
    change a.cell i + (if i = a.axis ∧ a.positive = true then 1 else 0) =
      b.cell i + (if i = b.axis ∧ b.positive = true then 1 else 0) at hi
    rw [ha, hp] at hi
    omega
  cases hap : a.positive <;> cases hbp : b.positive <;>
    simp [Facet.normal, hap, hbp] at hp ⊢

/-- The exact finite shared-facet predicate follows from collar identity and
inequality of the two owner cells. -/
theorem Pose.shared_of_gridFacet_eq {d : ℕ} {p : Pose d} {a b : Facet d}
    (hgrid : a.gridFacet = (p.facet b).gridFacet)
    (hcell : a.cell ≠ p.cell b.cell) : Shared p a b := by
  have ha : a.axis = (p.facet b).axis := congrArg GridFacet.axis hgrid
  refine ⟨(Facet.centre2_eq_of_gridFacet_eq hgrid).trans (p.facet_centre2 b), ?_, ?_⟩
  · rw [ha]
    exact p.perm.apply_symm_apply b.axis
  · have hn := Facet.normal_opposite_of_gridFacet_eq hgrid hcell
    rw [p.facet_normal, ← ha] at hn
    exact hn

/-- A common nonempty solid supported in the two respective facet collars
forces the finite `Shared` relation, provided the owner cells differ. -/
theorem Pose.shared_of_matched_solids {d : ℕ} {p : Pose d} {a b : Facet d}
    {A B : Set (Point d)} (hne : B.Nonempty)
    (hA : A ⊆ gridFacetCollar a.gridFacet)
    (hB : B ⊆ gridFacetCollar b.gridFacet)
    (heq : A = p.euclidean '' B) (hcell : a.cell ≠ p.cell b.cell) : Shared p a b := by
  rcases hne with ⟨x, hx⟩
  have hr : p.euclidean x ∈ gridFacetCollar a.gridFacet := by
    apply hA
    rw [heq]
    exact Set.mem_image_of_mem _ hx
  have hs := p.mapsTo_facet_collar b (hB hx)
  exact p.shared_of_gridFacet_eq (GridFacet.eq_of_mem_collars hr hs) hcell

#print axioms Pose.mapsTo_facet_collar
#print axioms Pose.shared_of_matched_solids
end SparseMonotiles.Contact
