module
public import PrimeFacetClosure.MinusAffine
@[expose] public section
namespace RegisteredPrime.PrimeFacetClosure
open Uniform

/-- The concrete residue -1 is nonsquare in every prime dimension 3 mod 4. -/
theorem minus_one_nonsquare {p : Nat} (hp : IsPrime p) (hmod : p % 4 = 3) :
    ¬ IsSquareMod p (p-1) := by
  have hp3 : 3 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have hg0 : ¬ p ∣ p-1 := IsPrime.not_dvd_of_pos_lt (by omega) (by omega)
  apply (U3_euler p (p-1) hp hp2 hg0).mp
  have hg : MEq p ((p-1 : Nat) : Int) (-1) := ⟨1, by omega⟩
  have hodd : ((p-1)/2) % 2 = 1 := by omega
  have hpow := hg.pow ((p-1)/2)
  rw [neg_one_pow_eq] at hpow
  simp only [hodd, Nat.one_ne_zero, ↓reduceIte] at hpow
  exact hpow.emod_eq

/-- The literal completed dense-family parameters. Its dimension is
judgmentally p, so the native dimension m+1 can instantiate it without casts. -/
def minusParameters (p : Nat) (hp : IsPrime p) (hmod : p % 4 = 3) : Parameters where
  p := p
  prime := hp
  odd := by omega
  mu := 1
  g := p-1
  mu_nonzero := IsPrime.not_dvd_of_pos_lt (by omega) (by have := hp.two_le; omega)
  mu_square := ⟨1, by simp⟩
  g_nonzero := IsPrime.not_dvd_of_pos_lt (by omega) (by omega)
  g_nonsquare := minus_one_nonsquare hp hmod

#print axioms minus_one_nonsquare
#print axioms minusParameters
end RegisteredPrime.PrimeFacetClosure
