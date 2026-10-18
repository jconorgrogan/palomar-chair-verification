module

public import SparseMonotiles.GridFacetCollars
public import SparseMonotiles.ContactChairChecker
public import SparseMonotiles.BoundaryInventory

@[expose] public section

/-!
# The literal carrier is a halfspace at every exposed unit facet

The owner cell and the absence of its integer neighbor are the only exposure
hypotheses. The proof goes through the actual union of binary closed cubes in
`Model.carrier`. Strict tangential coordinates force every contributing cube
to be one of the two cells adjacent to the facet; exposure excludes the other.

The comparison holds on the full open unit-cell neighborhood of the relative
interior of the facet. In particular it holds throughout the closed central
`gridFacetCollar`, and supplies a genuine `LocalSetEq` at every point of that
collar, including its boundary. No carrier-germ equivalence is assumed.
-/

namespace SparseMonotiles

open Set Filter
open scoped Topology

/-- A closed integer unit cube, with its lower corner recorded exactly. -/
def closedIntegerCell {d : ℕ} (c : Contact.Cell d) : Set (Point d) :=
  {x | ∀ i, (c i : ℝ) ≤ x i ∧ x i ≤ (c i : ℝ) + 1}

/-- The Boolean-cube definition of the physical carrier is precisely the
integer-cell union used by the finite contact checker. -/
theorem mem_carrier_iff_exists_chairCell {d : ℕ} (x : Point d) :
    x ∈ carrier d ↔ ∃ c : Contact.Cell d,
      Contact.IsChairCell c ∧ x ∈ closedIntegerCell c := by
  constructor
  · rintro ⟨b, hb, hx⟩
    refine ⟨Contact.binaryCell b, ⟨?_, ?_⟩, ?_⟩
    · intro i
      cases h : b i <;> simp [Contact.binaryCell, h]
    · rcases hb with ⟨i, hi⟩
      exact ⟨i, by simp [Contact.binaryCell, hi]⟩
    · intro i
      cases h : b i <;> simpa [Contact.binaryCell, h] using hx i
  · rintro ⟨c, ⟨hc, hz⟩, hx⟩
    let b : Fin d → Bool := fun i => decide (c i = 1)
    refine ⟨b, ?_, ?_⟩
    · rcases hz with ⟨i, hi⟩
      exact ⟨i, by simp [b, hi]⟩
    · intro i
      rcases hc i with hi | hi <;> simpa [b, hi] using hx i

namespace Contact.Facet

/-- Forget the outward orientation while retaining the integer supporting level. -/
def gridFacet {d : ℕ} (f : Facet d) : GridFacet d where
  axis := f.axis
  anchor i := f.cell i + if i = f.axis ∧ f.positive = true then 1 else 0

@[simp] theorem gridFacet_axis {d : ℕ} (f : Facet d) :
    f.gridFacet.axis = f.axis := rfl

@[simp] theorem gridFacet_anchor_tangent {d : ℕ} (f : Facet d)
    {i : Fin d} (hi : i ≠ f.axis) : f.gridFacet.anchor i = f.cell i := by
  simp [gridFacet, hi]

@[simp] theorem gridFacet_anchor_axis {d : ℕ} (f : Facet d) :
    f.gridFacet.anchor f.axis = f.cell f.axis + if f.positive then 1 else 0 := by
  cases h : f.positive <;> simp [gridFacet, h]

/-- Opposite orientations on one geometric facet cannot both be exposed chair
facets: one of the owner cells would be the other's absent neighbor. The stated
hypotheses are the minimal asymmetric pair needed for this conclusion. -/
theorem eq_of_gridFacet_eq {d : ℕ} {f g : Facet d}
    (hf : ¬ IsChairCell f.neighbor) (hg : IsChairCell g.cell)
    (hgrid : f.gridFacet = g.gridFacet) : f = g := by
  have ha : f.axis = g.axis := congrArg GridFacet.axis hgrid
  by_cases hp : f.positive = g.positive
  · apply Facet.ext ?_ ha hp
    funext i
    have hc := congrFun (congrArg GridFacet.anchor hgrid) i
    change f.cell i + (if i = f.axis ∧ f.positive = true then 1 else 0) =
      g.cell i + (if i = g.axis ∧ g.positive = true then 1 else 0) at hc
    rw [ha, hp] at hc
    omega
  · have hcell : g.cell = f.neighbor := by
      funext i
      have hc := congrFun (congrArg GridFacet.anchor hgrid) i
      by_cases hi : i = f.axis
      · have hi' : i = g.axis := hi.trans ha
        change f.cell i + (if i = f.axis ∧ f.positive = true then 1 else 0) =
          g.cell i + (if i = g.axis ∧ g.positive = true then 1 else 0) at hc
        have hfc : (if i = f.axis ∧ f.positive = true then (1 : ℤ) else 0) =
            (if f.positive then 1 else 0) := by simp [hi]
        have hgc : (if i = g.axis ∧ g.positive = true then (1 : ℤ) else 0) =
            (if g.positive then 1 else 0) := by simp [hi']
        rw [hfc, hgc] at hc
        change g.cell i = f.cell i + if i = f.axis then f.normal else 0
        rw [if_pos hi]
        cases hfp : f.positive <;> cases hgp : g.positive <;>
          simp [hfp, hgp, Facet.normal] at hc hp ⊢ <;> omega
      · have hi' : i ≠ g.axis := by simpa only [← ha] using hi
        simpa [gridFacet, Facet.neighbor, hi, hi'] using hc.symm
    exact (hf (hcell ▸ hg)).elim

/-- Forgetting orientation is injective on actual exposed carrier facets. -/
theorem gridFacet_injective_on_exposed (d : ℕ) :
    Function.Injective (fun f : {f : Facet d //
      IsChairCell f.cell ∧ ¬ IsChairCell f.neighbor} => f.val.gridFacet) := by
  intro f g h
  apply Subtype.ext
  exact eq_of_gridFacet_eq f.property.2 g.property.1 h

/-- The closed halfspace pointing into the owner cell. The recorded Boolean is
an outward-positive flag, so the positive case has an upper bound. -/
def inwardHalfspace {d : ℕ} (f : Facet d) : Set (Point d) :=
  {x | if f.positive then x f.axis ≤ (f.gridFacet.anchor f.axis : ℝ)
    else (f.gridFacet.anchor f.axis : ℝ) ≤ x f.axis}

/-- This local model is an actual closed coordinate halfspace. -/
theorem inwardHalfspace_isClosed {d : ℕ} (f : Facet d) :
    IsClosed f.inwardHalfspace := by
  have hcoord : Continuous (fun x : Point d => x f.axis) :=
    (continuous_apply f.axis).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  cases hp : f.positive
  · simpa only [inwardHalfspace, hp, Bool.false_eq_true, if_false] using
      (isClosed_le continuous_const hcoord :
        IsClosed {x : Point d | (f.gridFacet.anchor f.axis : ℝ) ≤ x f.axis})
  · simpa only [inwardHalfspace, hp, if_true] using
      (isClosed_le hcoord continuous_const :
        IsClosed {x : Point d | x f.axis ≤ (f.gridFacet.anchor f.axis : ℝ)})

/-- An open neighborhood of the entire relative interior of the unit facet.
The tangential inequalities are strict; their role is to exclude edge cells. -/
def openCellNeighborhood {d : ℕ} (f : Facet d) : Set (Point d) :=
  {x | |x f.axis - (f.gridFacet.anchor f.axis : ℝ)| < 1 ∧
    ∀ i, i ≠ f.axis → (f.cell i : ℝ) < x i ∧ x i < (f.cell i : ℝ) + 1}

/-- The relatively open unit facet, described without a relative-topology API. -/
def relativeInterior {d : ℕ} (f : Facet d) : Set (Point d) :=
  {x | x f.axis = (f.gridFacet.anchor f.axis : ℝ) ∧
    ∀ i, i ≠ f.axis → (f.cell i : ℝ) < x i ∧ x i < (f.cell i : ℝ) + 1}

theorem openCellNeighborhood_isOpen {d : ℕ} (f : Facet d) :
    IsOpen f.openCellNeighborhood := by
  have hcoord (i : Fin d) : Continuous (fun x : Point d => x i) :=
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  have hset : f.openCellNeighborhood =
      {x : Point d | |x f.axis - (f.gridFacet.anchor f.axis : ℝ)| < 1} ∩
      ⋂ i : Fin d, ⋂ (_ : i ≠ f.axis),
        {x : Point d | (f.cell i : ℝ) < x i ∧ x i < (f.cell i : ℝ) + 1} := by
    ext x
    simp only [openCellNeighborhood, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine (isOpen_lt (((hcoord f.axis).sub continuous_const).abs) continuous_const).inter ?_
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro _
  exact (isOpen_lt continuous_const (hcoord i)).inter (isOpen_lt (hcoord i) continuous_const)

theorem gridFacetCollar_subset_openCellNeighborhood {d : ℕ} (f : Facet d) :
    gridFacetCollar f.gridFacet ⊆ f.openCellNeighborhood := by
  intro x hx
  refine ⟨lt_of_le_of_lt hx.1 (by norm_num), ?_⟩
  intro i hi
  have ht := hx.2 i hi
  rw [f.gridFacet_anchor_tangent hi] at ht
  rcases abs_le.mp ht with ⟨hl, hu⟩
  constructor <;> linarith

theorem relativeInterior_subset_openCellNeighborhood {d : ℕ} (f : Facet d) :
    f.relativeInterior ⊆ f.openCellNeighborhood := by
  intro x hx
  refine ⟨?_, hx.2⟩
  rw [hx.1, sub_self, abs_zero]
  norm_num

private theorem integer_cell_tangent_unique {a c : ℤ} {x : ℝ}
    (ha : (a : ℝ) < x ∧ x < (a : ℝ) + 1)
    (hc : (c : ℝ) ≤ x ∧ x ≤ (c : ℝ) + 1) : c = a := by
  have hca : (c : ℝ) < (a : ℝ) + 1 := lt_of_le_of_lt hc.1 ha.2
  have hac : (a : ℝ) < (c : ℝ) + 1 := lt_of_lt_of_le ha.1 hc.2
  have hca' : c < a + 1 := by exact_mod_cast hca
  have hac' : a < c + 1 := by exact_mod_cast hac
  omega

private theorem integer_cell_normal_pair {a c : ℤ} {x : ℝ}
    (ha : |x - (a : ℝ)| < 1)
    (hc : (c : ℝ) ≤ x ∧ x ≤ (c : ℝ) + 1) : c = a - 1 ∨ c = a := by
  rcases abs_lt.mp ha with ⟨hl, hu⟩
  have hca : (c : ℝ) < (a : ℝ) + 1 := by linarith
  have hac : (a : ℝ) - 1 < (c : ℝ) + 1 := by linarith
  have hca' : c < a + 1 := by exact_mod_cast hca
  have hac' : a - 1 < c + 1 := by exact_mod_cast hac
  omega

/-- Inside the open facet neighborhood there are only two possible integer
owner cells. This is the geometric step that excludes every other carrier cube. -/
theorem cell_eq_owner_or_neighbor {d : ℕ} (f : Facet d) {c : Cell d} {x : Point d}
    (hx : x ∈ f.openCellNeighborhood) (hc : x ∈ closedIntegerCell c) :
    c = f.cell ∨ c = f.neighbor := by
  have ht : ∀ i, i ≠ f.axis → c i = f.cell i :=
    fun i hi => integer_cell_tangent_unique (hx.2 i hi) (hc i)
  have hn := integer_cell_normal_pair hx.1 (hc f.axis)
  have hn' : c f.axis = f.cell f.axis ∨ c f.axis = f.neighbor f.axis := by
    cases hp : f.positive <;>
      simp [gridFacet_anchor_axis, Facet.neighbor, Facet.normal, hp] at hn ⊢ <;> omega
  rcases hn' with hn' | hn'
  · left
    funext i
    by_cases hi : i = f.axis
    · simpa only [hi] using hn'
    · exact ht i hi
  · right
    funext i
    by_cases hi : i = f.axis
    · simpa only [hi] using hn'
    · simpa only [Facet.neighbor, if_neg hi, add_zero] using ht i hi

/-- The owner cube cuts this neighborhood out by exactly one inward inequality. -/
theorem mem_owner_iff_inwardHalfspace {d : ℕ} (f : Facet d) {x : Point d}
    (hx : x ∈ f.openCellNeighborhood) :
    x ∈ closedIntegerCell f.cell ↔ x ∈ f.inwardHalfspace := by
  constructor
  · intro hc
    have hn := hc f.axis
    cases hp : f.positive
    · simpa [inwardHalfspace, gridFacet_anchor_axis, hp] using hn.1
    · simpa [inwardHalfspace, gridFacet_anchor_axis, hp] using hn.2
  · intro hh i
    by_cases hi : i = f.axis
    · subst i
      have hn := hx.1
      rcases abs_lt.mp hn with ⟨hl, hu⟩
      cases hp : f.positive <;>
        simp [inwardHalfspace, gridFacet_anchor_axis, hp] at hh hl hu <;>
        constructor <;> linarith
    · exact ⟨(hx.2 i hi).1.le, (hx.2 i hi).2.le⟩

/-- Actual exposure of the owner cell proves the local carrier halfspace model;
there is no assumed equivalence or regularity premise. -/
theorem mem_carrier_iff_inwardHalfspace {d : ℕ} (f : Facet d)
    (howner : IsChairCell f.cell) (hexposed : ¬ IsChairCell f.neighbor)
    {x : Point d} (hx : x ∈ f.openCellNeighborhood) :
    x ∈ carrier d ↔ x ∈ f.inwardHalfspace := by
  rw [mem_carrier_iff_exists_chairCell]
  constructor
  · rintro ⟨c, hc, hxc⟩
    rcases f.cell_eq_owner_or_neighbor hx hxc with rfl | rfl
    · exact (f.mem_owner_iff_inwardHalfspace hx).mp hxc
    · exact (hexposed hc).elim
  · intro hh
    exact ⟨f.cell, howner, (f.mem_owner_iff_inwardHalfspace hx).mpr hh⟩

/-- The closed-collar membership theorem, including all collar boundary points. -/
theorem mem_carrier_iff_inwardHalfspace_of_mem_collar {d : ℕ} (f : Facet d)
    (howner : IsChairCell f.cell) (hexposed : ¬ IsChairCell f.neighbor)
    {x : Point d} (hx : x ∈ gridFacetCollar f.gridFacet) :
    x ∈ carrier d ↔ x ∈ f.inwardHalfspace :=
  f.mem_carrier_iff_inwardHalfspace howner hexposed
    (f.gridFacetCollar_subset_openCellNeighborhood hx)

/-- Exact equality of the two sets after restriction to the closed collar. -/
theorem carrier_inter_gridFacetCollar {d : ℕ} (f : Facet d)
    (howner : IsChairCell f.cell) (hexposed : ¬ IsChairCell f.neighbor) :
    carrier d ∩ gridFacetCollar f.gridFacet =
      f.inwardHalfspace ∩ gridFacetCollar f.gridFacet := by
  ext x
  constructor
  · rintro ⟨hc, hx⟩
    exact ⟨(f.mem_carrier_iff_inwardHalfspace_of_mem_collar howner hexposed hx).mp hc, hx⟩
  · rintro ⟨hh, hx⟩
    exact ⟨(f.mem_carrier_iff_inwardHalfspace_of_mem_collar howner hexposed hx).mpr hh, hx⟩

/-- A genuine carrier germ on an explicitly open facet neighborhood. -/
theorem localSetEq_carrier_inwardHalfspace {d : ℕ} (f : Facet d)
    (howner : IsChairCell f.cell) (hexposed : ¬ IsChairCell f.neighbor)
    {p : Point d} (hp : p ∈ f.openCellNeighborhood) :
    LocalSetEq p (carrier d) f.inwardHalfspace :=
  LocalSetEq.of_open f.openCellNeighborhood_isOpen hp
    (fun _ hx => f.mem_carrier_iff_inwardHalfspace howner hexposed hx)

/-- In particular, every point of the closed central collar has the exact
halfspace germ, even when it lies on the boundary of that collar. -/
theorem localSetEq_carrier_inwardHalfspace_of_mem_collar {d : ℕ} (f : Facet d)
    (howner : IsChairCell f.cell) (hexposed : ¬ IsChairCell f.neighbor)
    {p : Point d} (hp : p ∈ gridFacetCollar f.gridFacet) :
    LocalSetEq p (carrier d) f.inwardHalfspace :=
  f.localSetEq_carrier_inwardHalfspace howner hexposed
    (f.gridFacetCollar_subset_openCellNeighborhood hp)

/-- The same germ holds on the entire relative interior of an exposed unit facet. -/
theorem localSetEq_carrier_inwardHalfspace_of_relativeInterior {d : ℕ} (f : Facet d)
    (howner : IsChairCell f.cell) (hexposed : ¬ IsChairCell f.neighbor)
    {p : Point d} (hp : p ∈ f.relativeInterior) :
    LocalSetEq p (carrier d) f.inwardHalfspace :=
  f.localSetEq_carrier_inwardHalfspace howner hexposed
    (f.relativeInterior_subset_openCellNeighborhood hp)

/-- The exact isolated-key body model now has no unproved carrier-germ premise. -/
theorem localSetEq_body_isolated_halfspace {d : ℕ} (f : Facet d)
    (howner : IsChairCell f.cell) (hexposed : ¬ IsChairCell f.neighbor)
    {ks : List (KeyData d)} {k : KeyData d} {p : Point d}
    (hk : k ∈ ks) (hp : p ∈ gridFacetCollar f.gridFacet)
    (hiso : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j)
    {K : Set (Point d)} (hK : LocalSetEq p (keySolid k) K) :
    LocalSetEq p (body ks) (closure (keyReplacement f.inwardHalfspace K k.bump)) :=
  localSetEq_body_isolated_models hk hiso
    (f.localSetEq_carrier_inwardHalfspace_of_mem_collar howner hexposed hp) hK

/-- Away from all keys, the literal body has the proved carrier halfspace germ. -/
theorem localSetEq_body_away_keys_halfspace {d : ℕ} (f : Facet d)
    (howner : IsChairCell f.cell) (hexposed : ¬ IsChairCell f.neighbor)
    {ks : List (KeyData d)} {p : Point d} (hp : p ∈ gridFacetCollar f.gridFacet)
    (haway : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, x ∉ keySolid j) :
    LocalSetEq p (body ks) f.inwardHalfspace :=
  localSetEq_body_away_keys_model haway
    (f.localSetEq_carrier_inwardHalfspace_of_mem_collar howner hexposed hp)
    f.inwardHalfspace_isClosed

end Contact.Facet

#print axioms mem_carrier_iff_exists_chairCell
#print axioms Contact.Facet.eq_of_gridFacet_eq
#print axioms Contact.Facet.gridFacet_injective_on_exposed
#print axioms Contact.Facet.cell_eq_owner_or_neighbor
#print axioms Contact.Facet.mem_carrier_iff_inwardHalfspace_of_mem_collar
#print axioms Contact.Facet.carrier_inter_gridFacetCollar
#print axioms Contact.Facet.localSetEq_carrier_inwardHalfspace_of_relativeInterior
#print axioms Contact.Facet.localSetEq_body_isolated_halfspace
#print axioms Contact.Facet.localSetEq_body_away_keys_halfspace

end SparseMonotiles
