module
public import RegisteredPrime.CoarseGeometry
@[expose] public section
namespace RegisteredPrime
open Uniform

/-- The full finite-coordinate permutation is affine over F_p, with a
nonzero slope. No determinant or slope-subgroup restriction is imposed. -/
def RegisteredFrame.AffineIndex {p : Nat} (F : RegisteredFrame p) : Prop :=
  ∃ a : Nat, ∃ b : Int, ¬ p ∣ a ∧
    ∀ i : Fin p, MEq p (F.perm i).val ((a : Int) * i.val + b)

def Pose.AffineIndex {p : Nat} (q : Pose p) : Prop := q.frame.AffineIndex

theorem RegisteredFrame.AffineIndex.comp {p : Nat} (hp : IsPrime p)
    {F G : RegisteredFrame p} (hF : F.AffineIndex) (hG : G.AffineIndex) :
    (F.comp G).AffineIndex := by
  obtain ⟨a, b, ha, hF⟩ := hF
  obtain ⟨c, d, hc, hG⟩ := hG
  refine ⟨c * a, (c : Int) * b + d, hp.not_dvd_mul hc ha, fun i => ?_⟩
  have h := (hG (F.perm i)).trans
    (((MEq.refl (c : Int)).mul (hF i)).add (MEq.refl d))
  change MEq p (G.perm (F.perm i)).val _
  exact h.trans (MEq.of_eq (by simp only [Int.natCast_mul]; grind))

theorem RegisteredFrame.AffineIndex.inv {p : Nat} (hp : IsPrime p)
    {F : RegisteredFrame p} (hF : F.AffineIndex) : F.inv.AffineIndex := by
  obtain ⟨a, b, ha, hF⟩ := hF
  obtain ⟨hai, _, hian⟩ := invMod_spec hp ha
  let ai := invMod p a
  have hia : MEq p ((ai : Int) * a) 1 :=
    (MEq.of_eq (Int.mul_comm _ _)).trans hai
  refine ⟨ai, -((ai : Int) * b), hian, fun i => ?_⟩
  have he := hF (F.inverse i)
  rw [F.right_inverse] at he
  have hs := ((MEq.refl (ai : Int)).mul he).sub (MEq.refl ((ai : Int) * b))
  have ht := hia.mul (MEq.refl ((F.inverse i).val : Int))
  have hout : MEq p ((ai : Int) * i.val - (ai : Int) * b) (F.inverse i).val :=
    hs.trans ((MEq.of_eq (by grind)).trans (ht.trans (MEq.of_eq (by simp))))
  exact hout.symm.trans (MEq.of_eq (by omega))

theorem Pose.AffineIndex.comp {p : Nat} (hp : IsPrime p) {q r : Pose p}
    (hq : q.AffineIndex) (hr : r.AffineIndex) : (q.comp r).AffineIndex :=
  RegisteredFrame.AffineIndex.comp hp hq hr

theorem Pose.AffineIndex.inv {p : Nat} (hp : IsPrime p) {q : Pose p}
    (hq : q.AffineIndex) : q.inv.AffineIndex :=
  RegisteredFrame.AffineIndex.inv hp hq

theorem Pose.AffineIndex.relative {p : Nat} (hp : IsPrime p) {q r : Pose p}
    (hq : q.AffineIndex) (hr : r.AffineIndex) : (q.relative r).AffineIndex :=
  (hq.inv hp).comp hp hr

theorem Pose.Same.affine_index {p : Nat} {q r : Pose p} (he : q.Same r)
    (hq : q.AffineIndex) : r.AffineIndex := by
  obtain ⟨a, b, ha, hq⟩ := hq
  refine ⟨a, b, ha, fun i => ?_⟩
  rw [← he.1 i]
  exact hq i

theorem identity_affine_index {p : Nat} (hp : IsPrime p) :
    (identityPose p).AffineIndex := by
  refine ⟨1, 0, IsPrime.not_dvd_of_pos_lt (by omega) (by have := hp.two_le; omega),
    fun i => ?_⟩
  exact MEq.of_eq (by simp [identityPose])

/-- Every arithmetic child has an affine index permutation, including the
stipulated empty outer role f_empty(i)=μi. -/
theorem arithmeticChild_affine_index (P : Parameters) (r : Role P.p) :
    (arithmeticChild P r).AffineIndex := by
  classical
  cases r with
  | central =>
    refine ⟨P.mu, 0, P.mu_nonzero, fun i => ?_⟩
    rw [central_index_value]
    simpa only [Int.natCast_emod, Int.natCast_mul, Int.add_zero] using
      (MEq.emod_self (p := P.p) ((P.mu : Int) * i.val))
  | outer A hA =>
    by_cases hnA : NonemptyMask A
    · let k := suppCard P.p (extendMask A)
      let m := P.mu * P.g ^ k
      refine ⟨m, (m : Int) * ((P.p : Int) - zA P.p (extendMask A)),
        P.prime.not_dvd_mul P.mu_nonzero (P.prime.not_dvd_pow P.g_nonzero k), fun i => ?_⟩
      rw [outer_index_value P A hA hnA]
      exact lamPerm_affine P.p P.mu P.g (extendMask A)
        (Nat.le_of_lt (U1_zA P.p P.prime (extendMask A)
          (extend_nonempty_proper A hnA hA)).1) i.val
    · refine ⟨P.mu, 0, P.mu_nonzero, fun i => ?_⟩
      have he : ((arithmeticChild P (.outer A hA)).frame.perm i).val =
          (P.mu * i.val) % P.p := by
        simp [arithmeticChild, childIndex, childFrame, outerFrame, hnA, scalarFrame]
      rw [he]
      simpa only [Int.natCast_emod, Int.natCast_mul, Int.add_zero] using
        (MEq.emod_self (p := P.p) ((P.mu : Int) * i.val))

theorem refine_affine_index (P : Parameters) (q : Pose P.p) (r : Role P.p)
    (hq : q.AffineIndex) : (refine P q r).AffineIndex :=
  RegisteredFrame.AffineIndex.comp P.prime hq (arithmeticChild_affine_index P r)

/-- Arbitrary finite descendants preserve affine permutations; there is no
level bound or generated-contact catalog in this statement. -/
theorem descendant_affine_index (P : Parameters) (n : Nat) (q t : Pose P.p)
    (hq : q.AffineIndex) (ht : Descendant P n q t) : t.AffineIndex := by
  induction n generalizing q with
  | zero => exact ht.affine_index hq
  | succ n ih =>
    obtain ⟨r, hr⟩ := ht
    exact ih (refine P q r) (refine_affine_index P q r hq) hr

/-- The actual generated E language has affine index permutations. -/
theorem generated_contact_affine_index (P : Parameters) (e : Pose P.p)
    (he : GeneratedContact P e) : e.AffineIndex := by
  obtain ⟨n, q, r, hq, hr, _, he⟩ := he
  have hroot := identity_affine_index P.prime
  exact he.affine_index ((descendant_affine_index P n _ _ hroot hq).relative P.prime
    (descendant_affine_index P n _ _ hroot hr))

theorem parentCandidate_affine_index (P : Parameters) (a b : Role P.p) (k : Pose P.p)
    (hk : k.AffineIndex) : (parentCandidate P a b k).AffineIndex :=
  ((arithmeticChild_affine_index P a).comp P.prime hk).comp P.prime
    ((arithmeticChild_affine_index P b).inv P.prime)

/-- Every exact child-E-legal parent contact has an affine parent-relative
index permutation. This uses actual generated contacts, not an enlarged atlas. -/
theorem child_legal_parent_affine_index (P : Parameters) (t u : Pose P.p)
    (hc : DoubledFaceContact t u) (hl : ChildLegal P t u) :
    (t.relative u).AffineIndex := by
  obtain ⟨a, b, k, hk, he⟩ := child_legal_parent_candidate P t u hc hl
  rw [he]
  exact parentCandidate_affine_index P a b k (generated_contact_affine_index P k hk)

/-- A useful stronger bridge: even E-legality is unnecessary if every actual
cross-child contact is already known to have an affine index permutation. -/
theorem child_affine_parent_affine_index (P : Parameters) (t u : Pose P.p)
    (hc : DoubledFaceContact t u)
    (hl : ∀ a b : Role P.p,
      FaceContact (t.comp (arithmeticChild P a)) (u.comp (arithmeticChild P b)) →
      ((t.comp (arithmeticChild P a)).relative
        (u.comp (arithmeticChild P b))).AffineIndex) :
    (t.relative u).AffineIndex := by
  obtain ⟨a, b, hab⟩ := doubled_contact_child_witness P t u hc
  rw [← parent_candidate_reconstruction P t u a b]
  exact parentCandidate_affine_index P a b _ (hl a b hab)

end RegisteredPrime
