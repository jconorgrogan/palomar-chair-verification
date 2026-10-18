module

public import SparseMonotiles.ContactChecker

@[expose] public section

namespace SparseMonotiles.Contact

theorem ofFn_reindex_toFinset {α : Type*} [DecidableEq α] {n : ℕ}
    (f : Fin n → α) (e : Equiv.Perm (Fin n)) :
    (List.ofFn f).toFinset = (List.ofFn (fun i => f (e i))).toFinset := by
  apply Finset.ext
  intro x
  simp only [List.mem_toFinset, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by rw [e.apply_symm_apply]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e i, rfl⟩

#print axioms ofFn_reindex_toFinset
end SparseMonotiles.Contact
