module
public import RegisteredPrime.IncomingPredecessors
@[expose] public section
namespace RegisteredPrime
open Uniform
theorem balanced_mean_zero {p : Nat} (hp : IsPrime p) (D : Nat → Bool)
    (hD : NonemptyProperOn p D) (hbal : suppSum p D % p = 0) : zA p D = 0 := by
  have hp0 : 0 < p := by have := hp.two_le; omega
  have h := (U1_zA p hp D hD).2.2 0 hp0
  apply Eq.symm
  apply h
  simp [hbal]
theorem centered_image_balanced (p mu g : Nat) (hp : IsPrime p)
    (A : Nat → Bool) (hA : NonemptyProperOn p A) (τ : Nat → Nat)
    (hperm : IsPermOn p (lamPerm p mu g A))
    (hinv : ∀ i, i < p → τ (lamPerm p mu g A i) = i) :
    suppSum p (fun j => A (τ j)) % p = 0 := by
  have hz := U1_zA p hp A hA
  let m : Int := (mu * g ^ suppCard p A : Nat)
  have haff := fun i (_ : i < p) => lamPerm_affine p mu g A (by omega) i
  have hs := suppSum_affine hperm hinv A haff
  have hmean := MEq.of_nat_mod hz.2.1
  simp only [Int.natCast_mul] at hmean
  have hstep : MEq p
      (m * (suppSum p A : Int) + (m * ((p : Int) - (zA p A : Int))) * (suppCard p A : Int))
      (m * ((suppCard p A : Int) * (zA p A : Int)) +
        (m * ((p : Int) - (zA p A : Int))) * (suppCard p A : Int)) :=
    ((MEq.refl m).mul hmean.symm).add (MEq.refl _)
  have he : m * ((suppCard p A : Int) * (zA p A : Int)) +
      (m * ((p : Int) - (zA p A : Int))) * (suppCard p A : Int) =
      (p : Int) * (m * (suppCard p A : Int)) := by grind
  have hz0 : MEq p (suppSum p (fun j => A (τ j))) 0 :=
    hs.trans (hstep.trans ((MEq.of_eq he).trans (MEq.zero_of_dvd (Int.dvd_mul_right _ _))))
  have hnat : p ∣ suppSum p (fun j => A (τ j)) :=
    Int.natCast_dvd_natCast.mp hz0.dvd_of_zero
  exact Nat.mod_eq_zero_of_dvd hnat
noncomputable def boundedInverse (p : Nat) (σ : Nat → Nat) (hσ : IsPermOn p σ)
    (j : Nat) : Nat := by
  classical
  exact if hj : j < p then Classical.choose (hσ.surj j hj) else j
theorem boundedInverse_left {p : Nat} {σ : Nat → Nat} (hσ : IsPermOn p σ)
    (i : Nat) (hi : i < p) : boundedInverse p σ hσ (σ i) = i := by
  have hs := Classical.choose_spec (hσ.surj (σ i) (hσ.1 i hi))
  unfold boundedInverse
  simp only [hσ.1 i hi, dite_true]
  exact hσ.2 _ i hs.1 hi hs.2
theorem arithmetic_sign_image_balanced (P : Parameters) (A : Mask P.p)
    (hA : Proper A) (hnA : NonemptyMask A) :
    ∃ τ : Nat → Nat,
      (∀ i, i < P.p → τ (Uniform.lamPerm P.p P.mu P.g (extendMask A) i) = i) ∧
      suppSum P.p (fun j => extendMask A (τ j)) % P.p = 0 := by
  have hperm : IsPermOn P.p (lamPerm P.p P.mu P.g (extendMask A)) := by
    have h := (outerFrame_rotation P A hA).1
    simpa [outerFrame, hnA, lamChild] using h
  let τ := boundedInverse P.p (lamPerm P.p P.mu P.g (extendMask A)) hperm
  have hτ := boundedInverse_left hperm
  exact ⟨τ, hτ, centered_image_balanced P.p P.mu P.g P.prime (extendMask A)
    (extend_nonempty_proper A hnA hA) τ hperm hτ⟩
theorem balanced_hole_carry (p mu mui g a : Nat) (b : Int) (hp : IsPrime p)
    (D : Nat → Bool) (hD : NonemptyProperOn p D) (hbal : suppSum p D % p = 0)
    (σ τ : Nat → Nat) (hσ : IsPermOn p σ)
    (hτσ : ∀ i, i < p → τ (σ i) = i)
    (haff : ∀ i, i < p → MEq p (σ i) ((a : Int) * i + b))
    (hmu : (mu * mui) % p = 1)
    (haslope : (a * g ^ suppCard p D) % p = 1)
    (i : Nat) (hi : i < p) :
    lamPerm p mu g (fun j => D (τ j)) (σ ((mui * i) % p)) = i := by
  have hp2 := hp.two_le
  have hp0 : 0 < p := by omega
  let A : Nat → Bool := fun j => D (τ j)
  have hA : NonemptyProperOn p A := nonemptyProper_reindex hσ hτσ hD
  have hk : suppCard p A = suppCard p D := suppCard_reindex hσ hτσ D
  have hz : MEq p (zA p A) b := by
    have h := zA_affine hp hσ hτσ hD haff
    rw [balanced_mean_zero hp D hD hbal] at h
    simpa using h
  have hzbound := (U1_zA p hp A hA).1
  have hmu' : MEq p ((mu : Int) * mui) 1 := by
    have h := MEq.of_nat_mod (p := p) (a := mu * mui) (b := 1)
      (by rw [hmu, Nat.mod_eq_of_lt (by omega)])
    simpa only [Int.natCast_mul, Int.natCast_one] using h
  have ha' : MEq p ((a : Int) * (g : Int) ^ suppCard p D) 1 := by
    have h := MEq.of_nat_mod (p := p) (a := a * g ^ suppCard p D) (b := 1)
      (by rw [haslope, Nat.mod_eq_of_lt (by omega)])
    simpa only [Int.natCast_mul, Int.natCast_pow, Int.natCast_one] using h
  have hy : MEq p (((mui * i) % p : Nat) : Int) ((mui : Int) * i) := by
    rw [Int.natCast_emod, Int.natCast_mul]
    exact MEq.emod_self _
  have hs : MEq p (σ ((mui * i) % p)) ((a : Int) * ((mui : Int) * i) + b) :=
    (haff _ (Nat.mod_lt _ hp0)).trans (((MEq.refl (a : Int)).mul hy).add (MEq.refl b))
  have hl := lamPerm_affine p mu g A (by omega) (σ ((mui * i) % p))
  rw [hk] at hl
  let m : Int := (mu * g ^ suppCard p D : Nat)
  have hmid : MEq p
      (m * (σ ((mui * i) % p) : Int) + m * ((p : Int) - (zA p A : Int)))
      (m * ((a : Int) * ((mui : Int) * i) + b) + m * (0 - b)) :=
    ((MEq.refl m).mul hs).add ((MEq.refl m).mul
      ((MEq.zero_of_dvd (Int.dvd_refl (p : Int))).sub hz))
  have heq : m * ((a : Int) * ((mui : Int) * i) + b) + m * (0 - b) =
      ((mu : Int) * mui) * ((a : Int) * (g : Int) ^ suppCard p D) * i := by
    simp only [m, Int.natCast_mul, Int.natCast_pow]
    grind
  have hlast : MEq p (((mu : Int) * mui) * ((a : Int) * (g : Int) ^ suppCard p D) * i) i := by
    have h := (hmu'.mul ha').mul (MEq.refl (i : Int))
    simpa using h
  have hout := hl.trans (hmid.trans ((MEq.of_eq heq).trans hlast))
  have hlt := lamPerm_lt p mu g hp0 A (σ ((mui * i) % p))
  have he := hout.eq_of_lt (by omega) (by omega) (by omega) (by omega)
  change lamPerm p mu g A (σ ((mui * i) % p)) = i
  omega
theorem empty_hole_carry (p mu mui : Nat) (_hp : IsPrime p)
    (hmu : (mu * mui) % p = 1) (i : Nat) (hi : i < p) :
    mulMap p mu (mulMap p mui i) = i := by
  unfold mulMap
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc,
    Nat.mul_mod, hmu, Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hi]
end RegisteredPrime
