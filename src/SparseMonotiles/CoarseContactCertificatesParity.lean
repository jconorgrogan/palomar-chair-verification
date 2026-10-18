module

public import SparseMonotiles.CoarseContactCertificatesProduct

@[expose] public section

namespace SparseMonotiles.CarrierHierarchy
open Contact

theorem compose_shift_mod_two {d : ℕ} (p q : Pose d) (i : Fin d) :
    (compose p q).shift i % 2 = (p.shift i + q.shift (p.perm i)) % 2 := by
  rcases Bool.eq_false_or_eq_true (p.negative i) with h | h <;>
    simp [compose, Pose.sign, h] <;> omega

theorem inverse_shift_mod_two {d : ℕ} (p : Pose d) (i : Fin d) :
    (inversePose p).shift i % 2 = (-p.shift (p.perm.symm i)) % 2 := by
  rcases Bool.eq_false_or_eq_true (p.negative (p.perm.symm i)) with h | h <;>
    simp [inversePose, Pose.sign, h] <;> omega

theorem parentCandidate_shift_parity {d : ℕ} (a b k : Pose d) (pa pb pk : ℤ)
    (ha : ∀ i, a.shift i % 2 = pa % 2) (hb : ∀ i, b.shift i % 2 = pb % 2)
    (hk : ∀ i, k.shift i % 2 = pk % 2) (i : Fin d) :
    (parentCandidate a b k).shift i % 2 = (pa + pk - pb) % 2 := by
  have ho := compose_shift_mod_two a (compose k (inversePose b)) i
  have hi := compose_shift_mod_two k (inversePose b) (a.perm i)
  have hv := inverse_shift_mod_two b (k.perm (a.perm i))
  have hai := ha i
  have hki := hk (a.perm i)
  have hbi := hb (b.perm.symm (k.perm (a.perm i)))
  change (compose a (compose k (inversePose b))).shift i % 2 = _
  omega

/-- The odd branch checks only the three already bound anchor-parity bits. -/
def coarseParityAddressCheck {d : ℕ} {ρ : Type*} (lookup : ρ → Pose d)
    (a b k : Pose d) (pa pb pk : ℤ) : Option ρ → Bool
  | none => decide ((pa + pk - pb) % 2 ≠ 0)
  | some i => coarseProductMatchB a b k (lookup i)

theorem coarseParityAddressCheck_sound {d : ℕ} {ρ : Type*} (lookup : ρ → Pose d)
    (j : Fin d) {a b k : Pose d} {pa pb pk : ℤ}
    (ha : ∀ i, a.shift i % 2 = pa % 2) (hb : ∀ i, b.shift i % 2 = pb % 2)
    (hk : ∀ i, k.shift i % 2 = pk % 2) {address : Option ρ}
    (h : coarseParityAddressCheck lookup a b k pa pb pk address = true)
    (heven : ∀ i, (parentCandidate a b k).shift i % 2 = 0) :
    ∃ i, parentCandidate a b k = lookup i := by
  cases address with
  | none =>
      have hn : (pa + pk - pb) % 2 ≠ 0 := of_decide_eq_true h
      exact False.elim (hn ((parentCandidate_shift_parity a b k pa pb pk ha hb hk j).symm.trans
        (heven j)))
  | some i => exact ⟨i, coarseProductMatchB_sound h⟩

#print axioms parentCandidate_shift_parity
#print axioms coarseParityAddressCheck_sound
end SparseMonotiles.CarrierHierarchy
