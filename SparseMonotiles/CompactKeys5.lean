module

public import SparseMonotiles.CompactKeys5Chunks.Chunk00
public import SparseMonotiles.CompactKeys5Chunks.Chunk01
public import SparseMonotiles.CompactKeys5Chunks.Chunk02
public import SparseMonotiles.CompactKeys5Chunks.Chunk03
public import SparseMonotiles.CompactKeys5Chunks.Chunk04
public import SparseMonotiles.CompactKeys5Chunks.Chunk05
public import SparseMonotiles.CompactKeys5Chunks.Chunk06
public import SparseMonotiles.CompactKeys5Chunks.Chunk07
public import SparseMonotiles.CompactKeys5Chunks.Chunk08
public import SparseMonotiles.CompactKeys5Chunks.Chunk09
public import SparseMonotiles.CompactKeys5Chunks.Chunk10
public import SparseMonotiles.CompactKeys5Chunks.Chunk11
public import SparseMonotiles.CompactKeys5Chunks.Chunk12
public import SparseMonotiles.CompactKeys5Chunks.Chunk13
public import SparseMonotiles.CompactKeys5Chunks.Chunk14
public import SparseMonotiles.CompactKeys5Chunks.Chunk15
public import Mathlib.Tactic.FinCases

public section
namespace SparseMonotiles.CompactBinding.Keys5

theorem all_keys (i : Fin 256) : compactAt i = literalAt i := by
  have hall : ∀ b : Fin 16, ∀ j : Fin 16,
      compactAt (bindingIndex b j) = literalAt (bindingIndex b j) := by
    intro b
    fin_cases b
    · exact chunk0
    · exact chunk1
    · exact chunk2
    · exact chunk3
    · exact chunk4
    · exact chunk5
    · exact chunk6
    · exact chunk7
    · exact chunk8
    · exact chunk9
    · exact chunk10
    · exact chunk11
    · exact chunk12
    · exact chunk13
    · exact chunk14
    · exact chunk15
  let b : Fin 16 := ⟨i.val / 16, by omega⟩
  let j : Fin 16 := ⟨i.val % 16, by omega⟩
  have he : bindingIndex b j = i := by apply Fin.ext; simp only [bindingIndex, b, j]; omega
  simpa only [he] using hall b j

/-- Whole ordered key-list equality, proved from all bounded coordinate checks. -/
theorem keyList_eq : compactKeys = keys5 := by
  apply List.ext_getElem
  · rw [compactKeys_length, keys5_length]
  · intro i hi hj
    have h := all_keys ⟨i, by simpa only [compactKeys_length] using hi⟩
    exact h

/-- The compact independent body is the exact frozen literal S54 body. -/
theorem body_eq : PalomarMonotiles.T5 = SparseMonotiles.T5 := by
  calc
    PalomarMonotiles.T5 = SparseMonotiles.body compactKeys := (body_map _).symm
    _ = SparseMonotiles.body keys5 := congrArg SparseMonotiles.body keyList_eq
    _ = SparseMonotiles.T5 := rfl

/-- No physical quantifier or existence clause is weakened by the compact form. -/
theorem claim_iff : PalomarMonotiles.T5Claim ↔ SparseMonotiles.IsAperiodicMonotile SparseMonotiles.T5 := by
  change PalomarMonotiles.IsAperiodicMonotile PalomarMonotiles.T5 ↔ _
  rw [body_eq]
  exact (monotile_iff _).symm

#print axioms all_keys
#print axioms keyList_eq
#print axioms body_eq
#print axioms claim_iff
end SparseMonotiles.CompactBinding.Keys5
