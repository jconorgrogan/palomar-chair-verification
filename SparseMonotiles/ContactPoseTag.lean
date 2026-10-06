module

public import SparseMonotiles.ContactChecker
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace SparseMonotiles.Contact
open scoped BigOperators

/-- A computable catalogue tag. No global injectivity is assumed; the concrete
left-inverse certificate below establishes injectivity only on a finite table. -/
def Pose.finiteTag {d : ℕ} (p : Pose d) : ℕ :=
  (((∑ i : Fin d, (p.perm i).val * d ^ i.val) * 2 ^ d +
      ∑ i : Fin d, (if p.negative i then 1 else 0) * 2 ^ i.val) * 7 ^ d) +
    ∑ i : Fin d, (p.shift i + 2).toNat * 7 ^ i.val

theorem finite_table_injective_of_tag {α : Type*} {n : ℕ} (f : Fin n → α)
    (tag : α → ℕ) (lookup : ℕ → ℕ)
    (checked : ∀ i, lookup (tag (f i)) = i.val) : Function.Injective f := by
  intro i j h
  apply Fin.ext
  calc
    i.val = lookup (tag (f i)) := (checked i).symm
    _ = lookup (tag (f j)) := congrArg (fun x => lookup (tag x)) h
    _ = j.val := checked j

theorem finite_table_card {α : Type*} [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (unique : Function.Injective f) :
    (List.ofFn f).toFinset.card = n := by
  rw [← Fin.univ_image_def, Finset.card_image_of_injective _ unique]
  simp

#print axioms finite_table_injective_of_tag
#print axioms finite_table_card
end SparseMonotiles.Contact
