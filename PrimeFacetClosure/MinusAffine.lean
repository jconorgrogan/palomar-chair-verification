module
public import WorldExistence.ProperFrames
public import RegisteredPrime.ArithmeticAtlas
@[expose] public section

/-! Exact dihedral index control for the completed μ=1, g=-1 family.
The statements concern actual descendants/generated contacts, not a supplied
finite E catalogue or assumed facet closure. -/
namespace RegisteredPrime.PrimeFacetClosure
open Uniform

/-- An affine coordinate permutation with literal integer slope +1 or -1. -/
def SignedAffine {p : Nat} (F : RegisteredFrame p) : Prop :=
  ∃ s : Int, (s = 1 ∨ s = -1) ∧ ∃ b : Int,
    ∀ i : Fin p, MEq p (F.perm i).val (s * i.val + b)

theorem SignedAffine.comp {p : Nat} {F G : RegisteredFrame p}
    (hF : SignedAffine F) (hG : SignedAffine G) : SignedAffine (F.comp G) := by
  obtain ⟨s, hs, b, hF⟩ := hF
  obtain ⟨t, ht, c, hG⟩ := hG
  refine ⟨t*s, ?_, t*b+c, fun i => ?_⟩
  · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> decide
  · have h := (hG (F.perm i)).trans (((MEq.refl t).mul (hF i)).add (MEq.refl c))
    exact h.trans (MEq.of_eq (by grind))

theorem SignedAffine.inv {p : Nat} {F : RegisteredFrame p}
    (hF : SignedAffine F) : SignedAffine F.inv := by
  obtain ⟨s, hs, b, hF⟩ := hF
  refine ⟨s, hs, -(s*b), fun i => ?_⟩
  have h := hF (F.inverse i)
  rw [F.right_inverse] at h
  have hh := ((MEq.refl s).mul h).sub (MEq.refl (s*b))
  have he : s * (s * ((F.inverse i).val : Int) + b) - s*b = (F.inverse i).val := by
    rcases hs with rfl | rfl <;> grind
  rw [he] at hh
  exact hh.symm.trans (MEq.of_eq (by grind))

theorem identity_signedAffine (p : Nat) : SignedAffine (identityPose p).frame := by
  refine ⟨1, Or.inl rfl, 0, fun i => ?_⟩
  exact MEq.of_eq (by simp [identityPose])

theorem minus_parameter_congruence (P : Parameters) (hg : P.g = P.p - 1) :
    MEq P.p (P.g : Int) (-1) := by
  have hp := P.prime.two_le
  refine ⟨1, ?_⟩
  simp only [Int.mul_one]
  omega

theorem arithmeticChild_signedAffine (P : Parameters) (hm : P.mu = 1)
    (hg : P.g = P.p - 1) (r : Role P.p) : SignedAffine (arithmeticChild P r).frame := by
  classical
  cases r with
  | central =>
    refine ⟨1, Or.inl rfl, 0, fun i => ?_⟩
    rw [central_index_value, hm]
    exact MEq.of_eq (by simp [Nat.mod_eq_of_lt i.isLt])
  | outer A hA =>
    by_cases hnA : NonemptyMask A
    · let k := suppCard P.p (extendMask A)
      let s : Int := (-1)^k
      let z : Int := zA P.p (extendMask A)
      have hs : s = 1 ∨ s = -1 := neg_one_pow_cases k
      have hm' : MEq P.p ((P.mu * P.g^k : Nat) : Int) s := by
        simpa only [hm, Nat.one_mul, Int.natCast_pow] using
          (minus_parameter_congruence P hg).pow k
      refine ⟨s, hs, -(s*z), fun i => ?_⟩
      rw [outer_index_value P A hA hnA]
      have hz := (U1_zA P.p P.prime (extendMask A)
        (extend_nonempty_proper A hnA hA)).1
      have h := lamPerm_affine P.p P.mu P.g (extendMask A) (Nat.le_of_lt hz) i.val
      have hzero : MEq P.p (P.p : Int) 0 := MEq.zero_of_dvd (Int.dvd_refl _)
      have hh := (hm'.mul (MEq.refl (i.val : Int))).add
        (hm'.mul (hzero.sub (MEq.refl z)))
      exact h.trans (hh.trans (MEq.of_eq (by grind)))
    · refine ⟨1, Or.inl rfl, 0, fun i => ?_⟩
      have he : ((arithmeticChild P (.outer A hA)).frame.perm i).val = i.val := by
        simp [arithmeticChild, childIndex, childFrame, outerFrame, hnA,
          scalarFrame, hm, Nat.mod_eq_of_lt i.isLt]
      rw [he]
      exact MEq.of_eq (by simp)

theorem descendant_signedAffine (P : Parameters) (hm : P.mu = 1)
    (hg : P.g = P.p - 1) (n : Nat) (q t : Pose P.p)
    (hq : SignedAffine q.frame) (ht : Descendant P n q t) : SignedAffine t.frame := by
  induction n generalizing q with
  | zero => rw [← ht.eq]; exact hq
  | succ n ih =>
    obtain ⟨a, ha⟩ := ht
    exact ih (refine P q a) (hq.comp (arithmeticChild_signedAffine P hm hg a)) ha

/-- Actual generated contact permutations have only the two dihedral slopes. -/
theorem generated_signedAffine (P : Parameters) (hm : P.mu = 1)
    (hg : P.g = P.p - 1) (e : Pose P.p) (he : GeneratedContact P e) :
    SignedAffine e.frame := by
  obtain ⟨n, q, r, hq, hr, _, hs⟩ := he
  have hq' := descendant_signedAffine P hm hg n _ _ (identity_signedAffine _) hq
  have hr' := descendant_signedAffine P hm hg n _ _ (identity_signedAffine _) hr
  have h := hq'.inv.comp hr'
  rw [← hs.eq]
  exact h

/-- Properness of actual generated relative frames, with no catalogue input. -/
theorem generated_frame_proper (P : Parameters) (e : Pose P.p)
    (he : GeneratedContact P e) : e.frame.IsProper := by
  obtain ⟨n, q, r, hq, hr, _, hs⟩ := he
  have hq' := descendant_frame_proper P n _ _ (identity_frame_proper _) hq
  have hr' := descendant_frame_proper P n _ _ (identity_frame_proper _) hr
  rw [← hs.eq]
  exact hq'.inv.comp hr'

/-- Literal closure of the least generated language under actual cross-child
contacts, derived from its finite-descendant definition. -/
theorem generated_refinement_contact (P : Parameters) (e : Pose P.p)
    (he : GeneratedContact P e) (a b : Role P.p)
    (hc : FaceContact (arithmeticChild P a) (refine P e b)) :
    GeneratedContact P ((arithmeticChild P a).relative (refine P e b)) := by
  obtain ⟨n, q, r, hq, hr, _, hs⟩ := he
  rw [← hs.eq] at hc ⊢
  have hcontact := (doubleAnchor q).face_contact _ _ hc
  have hleft : (doubleAnchor q).comp (arithmeticChild P a) = refine P q a := rfl
  have hright : (doubleAnchor q).comp (refine P (q.relative r) b) = refine P r b := by
    rw [← refine_comp, Pose.comp_relative]
  rw [hleft, hright] at hcontact
  refine ⟨n+1, refine P q a, refine P r b,
    (descendant_succ_iff P n _ _).mpr ⟨q, a, hq, Pose.Same.refl _⟩,
    (descendant_succ_iff P n _ _).mpr ⟨r, b, hr, Pose.Same.refl _⟩,
    hcontact, ?_⟩
  rw [refine_relative]
  exact Pose.Same.refl _

#print axioms arithmeticChild_signedAffine
#print axioms descendant_signedAffine
#print axioms generated_signedAffine
#print axioms generated_frame_proper
#print axioms generated_refinement_contact
end RegisteredPrime.PrimeFacetClosure
