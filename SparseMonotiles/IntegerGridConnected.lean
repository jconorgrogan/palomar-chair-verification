module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Connectivity of the integer coordinate grid

A nonempty set of integer grid points that is closed under both unit steps in
every coordinate is the whole grid. The proof first iterates a step along an
integer coordinate, and then writes an arbitrary translation as a finite sum
of its single-coordinate parts. A reflexive-transitive-closure formulation
records finite point-to-point reachability.

These are purely combinatorial statements. In particular, they do not assert
that any set arising from a tiling is closed under coordinate steps. All results
include dimension zero, whose grid has a single point.
-/

namespace SparseMonotiles

/-- The standard integer unit vector along coordinate `i`. -/
def integerGridUnit {d : ℕ} (i : Fin d) : Fin d → ℤ := Pi.single i 1

@[simp] theorem integerGridUnit_self {d : ℕ} (i : Fin d) :
    integerGridUnit i i = 1 := by
  simp [integerGridUnit]

@[simp] theorem integerGridUnit_of_ne {d : ℕ} {i j : Fin d} (h : j ≠ i) :
    integerGridUnit i j = 0 := by
  simp [integerGridUnit, h]

/-- One positive or negative coordinate-unit step. -/
def IntegerGridStep {d : ℕ} (x y : Fin d → ℤ) : Prop :=
  ∃ i, y = x + integerGridUnit i ∨ y = x - integerGridUnit i

/-- Unit-step closure implies closure under an arbitrary integer step in one
coordinate. Neither nonemptiness nor a positive-dimension assumption is needed. -/
theorem integerGrid_mem_add_single_of_closed {d : ℕ} {S : Set (Fin d → ℤ)}
    (hadd : ∀ x ∈ S, ∀ i, x + integerGridUnit i ∈ S)
    (hsub : ∀ x ∈ S, ∀ i, x - integerGridUnit i ∈ S)
    {x : Fin d → ℤ} (hx : x ∈ S) (i : Fin d) (n : ℤ) :
    x + Pi.single i n ∈ S := by
  refine Int.inductionOn' n 0 ?_ ?_ ?_
  · simpa using hx
  · intro k _ hk
    rw [Pi.single_add, ← add_assoc]
    exact hadd (x + Pi.single i k) hk i
  · intro k _ hk
    rw [Pi.single_sub, ← add_sub_assoc]
    exact hsub (x + Pi.single i k) hk i

/-- Unit-step closure implies closure under every integer-grid translation. -/
theorem integerGrid_mem_add_of_closed {d : ℕ} {S : Set (Fin d → ℤ)}
    (hadd : ∀ x ∈ S, ∀ i, x + integerGridUnit i ∈ S)
    (hsub : ∀ x ∈ S, ∀ i, x - integerGridUnit i ∈ S)
    (v : Fin d → ℤ) {x : Fin d → ℤ} (hx : x ∈ S) : x + v ∈ S := by
  have htranslate : ∀ v : Fin d → ℤ, ∀ x ∈ S, x + v ∈ S := by
    intro w
    refine Pi.single_induction (fun v => ∀ x ∈ S, x + v ∈ S) w ?_ ?_ ?_
    · intro y hy
      simpa using hy
    · intro u v hu hv y hy
      simpa only [add_assoc] using hv (y + u) (hu y hy)
    · intro i n y hy
      exact integerGrid_mem_add_single_of_closed hadd hsub hy i n
  exact htranslate v x hx

/-- Every nonempty set closed under both directions of each coordinate-unit
step is the whole integer grid, including in dimension zero. -/
theorem integerGrid_eq_univ_of_closed {d : ℕ} {S : Set (Fin d → ℤ)}
    (hne : S.Nonempty)
    (hadd : ∀ x ∈ S, ∀ i, x + integerGridUnit i ∈ S)
    (hsub : ∀ x ∈ S, ∀ i, x - integerGridUnit i ∈ S) : S = Set.univ := by
  obtain ⟨x, hx⟩ := hne
  apply Set.eq_univ_of_forall
  intro y
  have hy := integerGrid_mem_add_of_closed hadd hsub (y - x) hx
  simpa only [add_sub_cancel] using hy

/-- The same conclusion with closure expressed using the adjacency relation. -/
theorem integerGrid_eq_univ_of_step_closed {d : ℕ} {S : Set (Fin d → ℤ)}
    (hne : S.Nonempty)
    (hstep : ∀ x ∈ S, ∀ y, IntegerGridStep x y → y ∈ S) : S = Set.univ := by
  apply integerGrid_eq_univ_of_closed hne
  · intro x hx i
    exact hstep x hx (x + integerGridUnit i) ⟨i, Or.inl rfl⟩
  · intro x hx i
    exact hstep x hx (x - integerGridUnit i) ⟨i, Or.inr rfl⟩

/-- Any two integer-grid points are joined by finitely many coordinate-unit
steps. Reflexivity supplies the empty path, including the dimension-zero case. -/
theorem integerGrid_reachable {d : ℕ} (x y : Fin d → ℤ) :
    Relation.ReflTransGen IntegerGridStep x y := by
  let S : Set (Fin d → ℤ) := {z | Relation.ReflTransGen IntegerGridStep x z}
  have hS : S = Set.univ := by
    apply integerGrid_eq_univ_of_step_closed (S := S)
    · exact ⟨x, Relation.ReflTransGen.refl⟩
    · intro a ha b hab
      exact ha.tail hab
  have hy : y ∈ S := by rw [hS]; exact Set.mem_univ y
  exact hy

#print axioms integerGrid_mem_add_single_of_closed
#print axioms integerGrid_mem_add_of_closed
#print axioms integerGrid_eq_univ_of_closed
#print axioms integerGrid_eq_univ_of_step_closed
#print axioms integerGrid_reachable

end SparseMonotiles
