module
public import T7DirectMatchedBlockCoverage
@[expose] public section
namespace SparseMonotiles.FullContactReplay
open T7DirectMatchedBlockCoverage

def RootRange (lo hi : Nat) : Prop := ∀ a : Fin 512, lo ≤ a.val → a.val < hi → ∀ b : Fin 512, PairLaw a b

theorem range_singleton (a : Fin 512) (h : ∀ b : Fin 512, PairLaw a b) : RootRange a.val (a.val + 1) := by
  intro x hlo hhi
  have he : x = a := by apply Fin.ext; omega
  exact he.symm ▸ h

theorem range_merge {lo mid hi : Nat} (left : RootRange lo mid) (right : RootRange mid hi) : RootRange lo hi := by
  intro a hlo hhi
  by_cases hm : a.val < mid
  · exact left a hlo hm
  · exact right a (by omega) hhi

theorem range_all (h : RootRange 0 512) : ∀ a b : Fin 512, PairLaw a b :=
  fun a => h a (Nat.zero_le _) a.isLt
#print axioms range_singleton
#print axioms range_merge
#print axioms range_all
end SparseMonotiles.FullContactReplay
