module

public import PhysicalRegistration.NativeChair
public import Mathlib.Topology.Constructions

@[expose] public section

/-! Literal finite integer polycubes. No boundary-registration assumptions. -/
namespace ProductClosure.Polycube
open Set
open scoped InnerProductSpace
noncomputable section

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev LatticeIndex (d : ℕ) := Fin d → ℤ
abbrev Cell {d : ℕ} (S : Finset (LatticeIndex d)) := {z // z ∈ S}

def latticeCell {d : ℕ} (z : LatticeIndex d) : Set (Space d) :=
  {x | ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ (z i : ℝ) + 1}

def openLatticeCell {d : ℕ} (z : LatticeIndex d) : Set (Space d) :=
  {x | ∀ i, (z i : ℝ) < x i ∧ x i < (z i : ℝ) + 1}

def latticeCenter {d : ℕ} (z : LatticeIndex d) : Space d :=
  WithLp.toLp 2 (fun i => (z i : ℝ) + 1 / 2)

def latticeStep {d : ℕ} (z : LatticeIndex d) (i : Fin d) (positive : Bool) :
    LatticeIndex d := fun k => z k + if k = i then (if positive then 1 else -1) else 0

def carrier {d : ℕ} (S : Finset (LatticeIndex d)) : Set (Space d) :=
  ⋃ c : Cell S, latticeCell c.val

/-- The finite occupied set is nonempty. Connectivity and ball topology are
separate properties, not smuggled into the cell representation. -/
structure FiniteCarrier (d : ℕ) where
  cells : Finset (LatticeIndex d)
  nonempty : cells.Nonempty

structure Facet {d : ℕ} (S : Finset (LatticeIndex d)) where
  cell : Cell S
  axis : Fin d
  positive : Bool
  outside : latticeStep cell.val axis positive ∉ S
  deriving DecidableEq

instance {d : ℕ} (S : Finset (LatticeIndex d)) : Fintype (Facet S) :=
  Fintype.ofInjective (fun f => (f.cell, f.axis, f.positive)) (by
    intro a b h
    cases a; cases b
    simp only [Prod.mk.injEq] at h
    obtain ⟨hc, hi, hp⟩ := h
    cases hc; cases hi; cases hp
    rfl)

def sign (positive : Bool) : ℝ := if positive then 1 else -1

def outward {d : ℕ} {S : Finset (LatticeIndex d)} (f : Facet S) : Space d :=
  sign f.positive • EuclideanSpace.single f.axis 1

def facetCenter {d : ℕ} {S : Finset (LatticeIndex d)} (f : Facet S) : Space d :=
  latticeCenter f.cell.val + (1 / 2 : ℝ) • outward f

def facetOutsideIndex {d : ℕ} {S : Finset (LatticeIndex d)} (f : Facet S) :
    LatticeIndex d := latticeStep f.cell.val f.axis f.positive

def facetPlane {d : ℕ} {S : Finset (LatticeIndex d)} (f : Facet S) : ℤ :=
  f.cell.val f.axis + if f.positive then 1 else 0

@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]

@[simp] theorem outward_apply {d : ℕ} {S : Finset (LatticeIndex d)}
    (f : Facet S) (k : Fin d) : outward f k = if k = f.axis then sign f.positive else 0 := by
  simp [outward]

@[simp] theorem facetCenter_normal {d : ℕ} {S : Finset (LatticeIndex d)} (f : Facet S) :
    facetCenter f f.axis = (facetPlane f : ℝ) := by
  cases hp : f.positive <;> simp [facetCenter, latticeCenter, facetPlane, sign, hp] <;> ring

@[simp] theorem facetCenter_tangent {d : ℕ} {S : Finset (LatticeIndex d)}
    (f : Facet S) (k : Fin d) (hk : k ≠ f.axis) :
    facetCenter f k = (f.cell.val k : ℝ) + 1 / 2 := by
  simp [facetCenter, latticeCenter, hk]

theorem facetInsideCell_center {d : ℕ} {S : Finset (LatticeIndex d)} (f : Facet S) :
    latticeCenter f.cell.val = facetCenter f - (1 / 2 : ℝ) • outward f := by
  unfold facetCenter
  module

theorem latticeCenter_step {d : ℕ} (z : LatticeIndex d) (i : Fin d) (b : Bool) :
    latticeCenter (latticeStep z i b) =
      latticeCenter z + sign b • EuclideanSpace.single i 1 := by
  ext k
  by_cases hki : k = i
  · subst k; cases b <;> simp [latticeCenter, latticeStep, sign] <;> ring
  · simp [latticeCenter, latticeStep, hki, Ne.symm hki]

theorem facetOutsideIndex_center {d : ℕ} {S : Finset (LatticeIndex d)} (f : Facet S) :
    latticeCenter (facetOutsideIndex f) = facetCenter f + (1 / 2 : ℝ) • outward f := by
  rw [facetOutsideIndex, latticeCenter_step]
  change latticeCenter f.cell.val + outward f = _
  unfold facetCenter
  module

/-- Exhaustive occupied-neighbor or exposed-boundary alternative. -/
theorem occupied_cell_neighbor {d : ℕ} {S : Finset (LatticeIndex d)}
    (c : Cell S) (i : Fin d) (b : Bool) :
    (∃ c' : Cell S, latticeStep c.val i b = c'.val) ∨
      ∃ f : Facet S, f.cell = c ∧ f.axis = i ∧ f.positive = b ∧
        latticeStep c.val i b = facetOutsideIndex f := by
  by_cases h : latticeStep c.val i b ∈ S
  · exact Or.inl ⟨⟨_, h⟩, rfl⟩
  · exact Or.inr ⟨⟨c, i, b, h⟩, rfl, rfl, rfl, rfl⟩

@[simp] theorem mem_carrier_iff {d : ℕ} (S : Finset (LatticeIndex d)) (x : Space d) :
    x ∈ carrier S ↔ ∃ z ∈ S, x ∈ latticeCell z := by
  simp [carrier]

theorem latticeCenter_mem_open {d : ℕ} (z : LatticeIndex d) :
    latticeCenter z ∈ openLatticeCell z := by
  intro i
  change (z i : ℝ) < (z i : ℝ) + 1 / 2 ∧ (z i : ℝ) + 1 / 2 < (z i : ℝ) + 1
  constructor <;> linarith

theorem openLatticeCell_subset {d : ℕ} (z : LatticeIndex d) :
    openLatticeCell z ⊆ latticeCell z := by
  intro x hx i
  exact ⟨(hx i).1.le, (hx i).2.le⟩

theorem latticeCell_compact {d : ℕ} (z : LatticeIndex d) : IsCompact (latticeCell z) := by
  have h := (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph.isCompact_preimage.mpr
    (isCompact_Icc (a := fun i => (z i : ℝ)) (b := fun i => (z i : ℝ) + 1))
  convert h using 1
  ext x
  simp only [latticeCell, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def]
  exact forall_and

theorem carrier_compact {d : ℕ} (S : Finset (LatticeIndex d)) : IsCompact (carrier S) :=
  isCompact_iUnion (fun c : Cell S => latticeCell_compact c.val)

theorem carrier_nonempty {d : ℕ} {S : Finset (LatticeIndex d)} (hS : S.Nonempty) :
    (carrier S).Nonempty := by
  obtain ⟨z, hz⟩ := hS
  exact ⟨latticeCenter z, (mem_carrier_iff _ _).mpr
    ⟨z, hz, openLatticeCell_subset z (latticeCenter_mem_open z)⟩⟩

theorem interior_latticeCell {d : ℕ} (z : LatticeIndex d) :
    interior (latticeCell z) = openLatticeCell z := by
  let e := (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph
  have hc : latticeCell z = e ⁻¹' (Set.pi Set.univ (fun i => Icc (z i : ℝ) ((z i : ℝ) + 1))) := by
    ext x; simp [latticeCell, e, Pi.le_def, ← forall_and]
  rw [hc, ← e.preimage_interior, interior_pi_set (Set.finite_univ)]
  ext x
  simp [openLatticeCell, interior_Icc, e]

/-- Distinct integer cells have disjoint actual Euclidean interiors. -/
theorem interiors_disjoint_iff {d : ℕ} (z w : LatticeIndex d) :
    Disjoint (interior (latticeCell z)) (interior (latticeCell w)) ↔ z ≠ w := by
  rw [interior_latticeCell, interior_latticeCell]
  constructor
  · intro h heq
    subst w
    exact Set.disjoint_left.mp h (latticeCenter_mem_open z) (latticeCenter_mem_open z)
  · intro hzw
    apply Set.disjoint_left.mpr
    intro x hx hy
    have heq : z = w := by
      funext i
      have hzi := hx i
      have hwi := hy i
      have h₁ : (z i : ℝ) < (w i : ℝ) + 1 := lt_trans hzi.1 hwi.2
      have h₂ : (w i : ℝ) < (z i : ℝ) + 1 := lt_trans hwi.1 hzi.2
      have h₁' : z i < w i + 1 := by exact_mod_cast h₁
      have h₂' : w i < z i + 1 := by exact_mod_cast h₂
      omega
    exact hzw heq

end
end ProductClosure.Polycube
