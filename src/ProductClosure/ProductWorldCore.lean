module

public import PhysicalRegistration.LatticeStepConnectivity

@[expose] public section

/-!
# Complete cell worlds and product contact languages

A world here is an actual partition of the full lattice by nonempty placed
cell footprints. Its owner function is derived from coverage and disjointness.
The state type may include the complete placed frame; no quotient by occupied
sets is taken. Cartesian factorization will be derived in `ProductWorld`.
-/
namespace ProductClosure.World

open Set
noncomputable section

universe u v w

/-- Complete, nonoverlapping cell tiling, with no empty phantom tiles. -/
structure CompleteTiling {X : Type u} {State : Type v} (cells : State → Set X) where
  tiles : Set State
  cover : ∀ x, ∃ t ∈ tiles, x ∈ cells t
  disjoint : ∀ t ∈ tiles, ∀ s ∈ tiles, t ≠ s → Disjoint (cells t) (cells s)
  nonempty : ∀ t ∈ tiles, (cells t).Nonempty

namespace CompleteTiling
variable {X : Type u} {State : Type v} {cells : State → Set X}

/-- The unique tile owning a lattice cell. -/
def owner (W : CompleteTiling cells) (x : X) : State := (W.cover x).choose

theorem owner_mem (W : CompleteTiling cells) (x : X) : W.owner x ∈ W.tiles :=
  (W.cover x).choose_spec.1

theorem mem_owner (W : CompleteTiling cells) (x : X) : x ∈ cells (W.owner x) :=
  (W.cover x).choose_spec.2

theorem owner_eq_of_mem (W : CompleteTiling cells) {x : X} {t : State}
    (ht : t ∈ W.tiles) (hx : x ∈ cells t) : W.owner x = t := by
  by_contra h
  exact Set.disjoint_left.mp (W.disjoint _ (W.owner_mem x) _ ht h)
    (W.mem_owner x) hx

theorem mem_cells_iff_owner (W : CompleteTiling cells) {t : State}
    (ht : t ∈ W.tiles) (x : X) : x ∈ cells t ↔ W.owner x = t := by
  constructor
  · exact W.owner_eq_of_mem ht
  · intro h
    simpa [h] using W.mem_owner x

theorem tiles_eq_range_owner (W : CompleteTiling cells) : W.tiles = Set.range W.owner := by
  ext t
  constructor
  · intro ht
    obtain ⟨x, hx⟩ := W.nonempty t ht
    exact ⟨x, W.owner_eq_of_mem ht hx⟩
  · rintro ⟨x, rfl⟩
    exact W.owner_mem x

/-- Every actual contact between distinct cell owners obeys the language. -/
def IsLegal (W : CompleteTiling cells) (adjacent : X → X → Prop)
    (language : State → State → Prop) : Prop :=
  ∀ x y, adjacent x y → W.owner x ≠ W.owner y → language (W.owner x) (W.owner y)

end CompleteTiling

abbrev Lattice (d : ℕ) := Fin d → ℤ

def latticeStep {d : ℕ} (z : Lattice d) (i : Fin d) (positive : Bool) : Lattice d :=
  fun k => z k + if k = i then (if positive then 1 else -1) else 0

def LatticeAdjacent {d : ℕ} (x y : Lattice d) : Prop :=
  ∃ i b, y = latticeStep x i b

/-- Constancy on literal positive and negative unit steps implies global
constancy, including dimension zero. This uses finite integer-coordinate
connectivity, not a topological generic-section assumption. -/
theorem eq_of_latticeStep_invariant {d : ℕ} {State : Type u}
    (f : Lattice d → State)
    (hstep : ∀ x i b, f (latticeStep x i b) = f x) (x y : Lattice d) : f x = f y := by
  cases d with
  | zero => exact congrArg f (Subsingleton.elim x y)
  | succ d =>
    have hu : {z : Lattice (d + 1) | f z = f y} = Set.univ :=
      PhysicalRegistration.NativeChair.eq_univ_of_nonempty_latticeStep_closed
        {z | f z = f y} ⟨y, rfl⟩ (by
          intro z hz i b
          change f (latticeStep z i b) = f y
          exact (hstep z i b).trans hz)
    have hx : x ∈ {z : Lattice (d + 1) | f z = f y} := by rw [hu]; trivial
    exact hx

/-- Literal product of occupied cell sets. -/
def productCells {X : Type u} {Y : Type v} {A : Type w} {B : Type*}
    (cellsA : A → Set X) (cellsB : B → Set Y) (t : A × B) : Set (X × Y) :=
  cellsA t.1 ×ˢ cellsB t.2

/-- A product mate changes exactly one factor and preserves the complete
placed state of the other factor, including its frame and translation. -/
def ProductLanguage {A : Type u} {B : Type v}
    (MA : A → A → Prop) (MB : B → B → Prop) (p q : A × B) : Prop :=
  (MA p.1 q.1 ∧ p.2 = q.2) ∨ (p.1 = q.1 ∧ MB p.2 q.2)

/-- The coordinate-neighbor relation in the split full integer lattice. -/
def ProductAdjacent {m n : ℕ} (p q : Lattice m × Lattice n) : Prop :=
  (LatticeAdjacent p.1 q.1 ∧ p.2 = q.2) ∨
  (p.1 = q.1 ∧ LatticeAdjacent p.2 q.2)

/-- Geometric contact legality includes disjointness of the factor interiors,
and hence disjointness of their occupied lattice cells. -/
def Separates {X : Type u} {A : Type v} (cells : A → Set X)
    (M : A → A → Prop) : Prop := ∀ a b, M a b → Disjoint (cells a) (cells b)

end
end ProductClosure.World
