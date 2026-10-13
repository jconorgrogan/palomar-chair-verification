module

public import PhysicalRegistration.NativeLatticeCells

@[expose] public section

/-!
# Connectivity of the literal integer cell lattice

A nonempty collection of integer-indexed cells closed under each positive
and negative unit coordinate step is all cells. The proof changes one
integer coordinate at a time and then performs finitely many such changes.
There is no hypothesis that a tiling component or its carriers cover space.
-/

namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- Closure under the two literal lattice steps permits any integer shift
in a single coordinate. -/
theorem mem_of_latticeStep_closed_shift {m : ℕ} (W : Set (LatticeIndex m))
    (hstep : ∀ z ∈ W, ∀ i b, latticeStep z i b ∈ W)
    {z : LatticeIndex m} (hz : z ∈ W) (i : Fin (m + 1)) (d : ℤ) :
    (fun k => z k + if k = i then d else 0) ∈ W := by
  induction d using Int.induction_on with
  | zero => simpa using hz
  | succ n ih =>
    convert hstep _ ih i true using 1
    funext k
    by_cases hki : k = i <;> simp [latticeStep, hki, add_assoc]
  | pred n ih =>
    convert hstep _ ih i false using 1
    funext k
    by_cases hki : k = i <;> simp [latticeStep, hki, add_assoc, sub_eq_add_neg]

/-- Closure under unit lattice steps permits replacing one coordinate by
any prescribed integer, without changing the other coordinates. -/
theorem mem_of_latticeStep_closed_update {m : ℕ} (W : Set (LatticeIndex m))
    (hstep : ∀ z ∈ W, ∀ i b, latticeStep z i b ∈ W)
    {z : LatticeIndex m} (hz : z ∈ W) (i : Fin (m + 1)) (t : ℤ) :
    Function.update z i t ∈ W := by
  convert mem_of_latticeStep_closed_shift W hstep hz i (t - z i) using 1
  funext k
  by_cases hki : k = i
  · subst k
    simp
  · simp [hki]

/-- Finitely many coordinate replacements remain in any step-closed set. -/
theorem mem_of_latticeStep_closed_finset {m : ℕ} (W : Set (LatticeIndex m))
    (hstep : ∀ z ∈ W, ∀ i b, latticeStep z i b ∈ W)
    {z : LatticeIndex m} (hz : z ∈ W) (y : LatticeIndex m)
    (s : Finset (Fin (m + 1))) :
    (fun k => if k ∈ s then y k else z k) ∈ W := by
  induction s using Finset.induction_on with
  | empty => simpa using hz
  | @insert i s his ih =>
    convert mem_of_latticeStep_closed_update W hstep ih i (y i) using 1
    funext k
    by_cases hki : k = i
    · subst k
      simp
    · simp [hki]

/-- The integer unit-cell lattice has no proper nonempty subset closed under
every positive and negative coordinate-neighbor step. -/
theorem eq_univ_of_nonempty_latticeStep_closed {m : ℕ}
    (W : Set (LatticeIndex m)) (hne : W.Nonempty)
    (hstep : ∀ z ∈ W, ∀ i b, latticeStep z i b ∈ W) : W = univ := by
  obtain ⟨z, hz⟩ := hne
  apply Set.eq_univ_of_forall
  intro y
  simpa using mem_of_latticeStep_closed_finset W hstep hz y Finset.univ

#print axioms mem_of_latticeStep_closed_shift
#print axioms mem_of_latticeStep_closed_update
#print axioms mem_of_latticeStep_closed_finset
#print axioms eq_univ_of_nonempty_latticeStep_closed

end
end PhysicalRegistration.NativeChair
