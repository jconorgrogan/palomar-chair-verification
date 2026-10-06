module

public import SparseMonotiles.CarrierHierarchyCoarseCandidates

@[expose] public section

/-!
Small Boolean refinements for independently exported coarse-contact data.
Every checked coordinate is related to the actual signed-affine Pose value.
No external decision procedure, opaque evaluation axiom, or search cutoff is used.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Coordinate-local equality, avoiding dependent permutation-equality reduction. -/
def coarsePoseMatchB {d : ℕ} (p q : Pose d) : Bool :=
  (List.finRange d).all fun i =>
    decide (p.perm i = q.perm i) &&
    decide (p.negative i = q.negative i) &&
    decide (p.shift i = q.shift i)

theorem coarsePoseMatchB_sound {d : ℕ} {p q : Pose d}
    (h : coarsePoseMatchB p q = true) : p = q := by
  have hf : ∀ i, p.perm i = q.perm i ∧ p.negative i = q.negative i ∧
      p.shift i = q.shift i := by
    simpa [coarsePoseMatchB, List.all_eq_true, and_assoc] using h
  have hp : p.perm = q.perm := Equiv.ext fun i => (hf i).1
  have hn : p.negative = q.negative := funext fun i => (hf i).2.1
  have hs : p.shift = q.shift := funext fun i => (hf i).2.2
  cases p
  cases q
  simp only [Pose.mk.injEq] at *
  exact ⟨hp, hn, hs⟩

def coarseAllB {n : ℕ} (check : Fin n → Bool) : Bool :=
  (List.finRange n).all check

theorem coarseAllB_sound {n : ℕ} {check : Fin n → Bool}
    (h : coarseAllB check = true) (i : Fin n) : check i = true :=
  List.all_eq_true.mp h i (List.mem_finRange i)

/-- An odd generated offset cannot occur after the geometric alignment theorem.
Otherwise the supplied address must reproduce the whole generated parent pose. -/
def coarseAddressCheck {d : ℕ} {ρ : Type*} (lookup : ρ → Pose d)
    (a b k : Pose d) : Option ρ → Bool
  | none => decide (∃ i, (parentCandidate a b k).shift i % 2 ≠ 0)
  | some i => coarsePoseMatchB (parentCandidate a b k) (lookup i)

theorem coarseAddressCheck_sound {d : ℕ} {ρ : Type*} (lookup : ρ → Pose d)
    {a b k : Pose d} {address : Option ρ}
    (h : coarseAddressCheck lookup a b k address = true)
    (heven : ∀ i, (parentCandidate a b k).shift i % 2 = 0) :
    ∃ i, parentCandidate a b k = lookup i := by
  cases address with
  | none =>
      obtain ⟨i, hi⟩ := of_decide_eq_true h
      exact False.elim (hi (heven i))
  | some i => exact ⟨i, coarsePoseMatchB_sound h⟩

#print axioms coarsePoseMatchB_sound
#print axioms coarseAddressCheck_sound
end SparseMonotiles.CarrierHierarchy
