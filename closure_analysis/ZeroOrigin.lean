module
public import closure_analysis.ZeroOriginGeometry
public import MeanObstruction.AffineFrames
public import MeanObstruction.Complement
@[expose] public section
namespace RegisteredPrime
open Uniform

/-- Coordinate 0 in the finite coordinate set of a permitted parameter. -/
def zeroIndex (P : Parameters) : Fin P.p :=
  ⟨0, by have := P.prime.two_le; omega⟩

/-- The small extra invariant needed beyond carrier recognition. -/
def Pose.ZeroOrigin (P : Parameters) (e : Pose P.p) : Prop :=
  e.frame.perm (zeroIndex P) = zeroIndex P

noncomputable def maskMeanIndex (P : Parameters) (A : Mask P.p)
    (hA : Proper A) (hnA : NonemptyMask A) : Fin P.p :=
  ⟨zA P.p (extendMask A),
    (U1_zA P.p P.prime (extendMask A) (extend_nonempty_proper A hnA hA)).1⟩

/-- Every finite frame extends to a bounded permutation on the Nat model. -/
theorem RegisteredFrame.toUniform_isPerm {p : Nat} (F : RegisteredFrame p) :
    IsPermOn p F.toUniform.perm := by
  constructor
  · intro i hi
    simp [RegisteredFrame.toUniform, hi]
  · intro i j hi hj hij
    have he : F.perm ⟨i, hi⟩ = F.perm ⟨j, hj⟩ := by
      apply Fin.ext
      simpa [RegisteredFrame.toUniform, hi, hj] using hij
    have he' := congrArg F.inverse he
    rw [F.left_inverse, F.left_inverse] at he'
    exact congrArg Fin.val he'

theorem RegisteredFrame.toUniform_inverse {p : Nat} (F : RegisteredFrame p)
    (i : Nat) (hi : i < p) : F.inv.toUniform.perm (F.toUniform.perm i) = i := by
  simp [RegisteredFrame.toUniform, hi, (F.perm ⟨i, hi⟩).isLt,
    RegisteredFrame.inv, F.left_inverse]

/-- Affine covariance of means, in the actual Fin-coordinate interface. -/
theorem affine_mask_mean_index (P : Parameters) (F : RegisteredFrame P.p)
    (hF : F.AffineIndex) (A B : Mask P.p) (hA : Proper A) (hnA : NonemptyMask A)
    (hB : Proper B) (hnB : NonemptyMask B)
    (hAB : ∀ i, B (F.perm i) = A i) :
    F.perm (maskMeanIndex P A hA hnA) = maskMeanIndex P B hB hnB := by
  obtain ⟨a, b, _, hF⟩ := hF
  have hcov := zA_affine P.prime F.toUniform_isPerm F.toUniform_inverse
    (extend_nonempty_proper A hnA hA)
    (fun i hi => by simpa [RegisteredFrame.toUniform, hi] using hF ⟨i, hi⟩)
  have hmeans : zA P.p (fun j => extendMask A (F.inv.toUniform.perm j)) =
      zA P.p (extendMask B) := by
    apply mean_congr_support
    intro j hj
    have he := hAB (F.inverse ⟨j, hj⟩)
    rw [F.right_inverse] at he
    simpa [RegisteredFrame.toUniform, RegisteredFrame.inv, hj,
      (F.inverse ⟨j, hj⟩).isLt, extendMask] using he.symm
  rw [hmeans] at hcov
  have hf := hF (maskMeanIndex P A hA hnA)
  have he : MEq P.p (F.perm (maskMeanIndex P A hA hnA)).val
      (maskMeanIndex P B hB hnB).val := hf.trans hcov.symm
  apply Fin.ext
  have hfl := (F.perm (maskMeanIndex P A hA hnA)).isLt
  have hbl := (maskMeanIndex P B hB hnB).isLt
  have hei := he.eq_of_lt (by omega) (by omega) (by omega) (by omega)
  omega

/-- The nonempty role's centering is literal: its mean maps to index zero. -/
theorem outer_index_mean_zero (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (hnA : NonemptyMask A) :
    (arithmeticChild P (.outer A hA)).frame.perm (maskMeanIndex P A hA hnA) =
      zeroIndex P := by
  apply Fin.ext
  rw [outer_index_value P A hA hnA]
  change (P.mu * P.g ^ suppCard P.p (extendMask A) *
    (zA P.p (extendMask A) + P.p - zA P.p (extendMask A))) % P.p = 0
  rw [show zA P.p (extendMask A) + P.p - zA P.p (extendMask A) = P.p by omega]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left P.p _)

theorem outer_inverse_zero_mean (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (hnA : NonemptyMask A) :
    (arithmeticChild P (.outer A hA)).frame.inverse (zeroIndex P) =
      maskMeanIndex P A hA hnA := by
  rw [← outer_index_mean_zero P A hA hnA]
  exact (arithmeticChild P (.outer A hA)).frame.left_inverse _

theorem central_index_zero (P : Parameters) :
    (arithmeticChild P .central).frame.perm (zeroIndex P) = zeroIndex P := by
  apply Fin.ext
  simp [central_index_value, zeroIndex]

theorem central_inverse_zero (P : Parameters) :
    (arithmeticChild P .central).frame.inverse (zeroIndex P) = zeroIndex P := by
  rw [← central_index_zero P]
  exact (arithmeticChild P .central).frame.left_inverse _

/-- The arithmetic conclusion from any exact parent-to-child mean equation. -/
theorem outer_relative_zero_of_mean (P : Parameters) (e : Pose P.p)
    (A B : Mask P.p) (hA : Proper A) (hnA : NonemptyMask A)
    (hB : Proper B) (hnB : NonemptyMask B)
    (hm : e.frame.perm (maskMeanIndex P A hA hnA) = maskMeanIndex P B hB hnB) :
    ((arithmeticChild P (.outer A hA)).relative (refine P e (.outer B hB))).ZeroOrigin P := by
  change (arithmeticChild P (.outer B hB)).frame.perm
    (e.frame.perm ((arithmeticChild P (.outer A hA)).frame.inverse (zeroIndex P))) = zeroIndex P
  rw [outer_inverse_zero_mean P A hA hnA, hm, outer_index_mean_zero P B hB hnB]

/-- Equal pulled-back roles preserve zero origin; empty roles use exactly
one smaller-depth zero-origin hypothesis, and are never assigned a mean. -/
theorem outer_relative_zero_equal (P : Parameters) (e : Pose P.p) (he : e.AffineIndex)
    (A B : Mask P.p) (hA : Proper A) (hB : Proper B)
    (hAB : ∀ i, B (e.frame.perm i) = A i)
    (hzero : A = (fun _ => false) → e.ZeroOrigin P) :
    ((arithmeticChild P (.outer A hA)).relative (refine P e (.outer B hB))).ZeroOrigin P := by
  classical
  by_cases hnA : NonemptyMask A
  · obtain ⟨i, hi⟩ := hnA
    have hnB : NonemptyMask B := ⟨e.frame.perm i, (hAB i).trans hi⟩
    exact outer_relative_zero_of_mean P e A B hA ⟨i, hi⟩ hB hnB
      (affine_mask_mean_index P e.frame he A B hA ⟨i, hi⟩ hB hnB hAB)
  · have hA0 : A = fun _ => false := by
      funext i
      cases hi : A i
      · rfl
      · exact False.elim (hnA ⟨i, hi⟩)
    have hB0 : B = fun _ => false := by
      funext i
      have hi := hAB (e.frame.inverse i)
      rw [e.frame.right_inverse, hA0] at hi
      exact hi
    have hz := hzero hA0
    subst A
    subst B
    change (arithmeticChild P (.outer (fun _ => false) hB)).frame.perm
      (e.frame.perm ((arithmeticChild P (.outer (fun _ => false) hA)).frame.inverse
        (zeroIndex P))) = zeroIndex P
    rw [empty_child_frame, central_inverse_zero P, hz, central_index_zero P]

/-- Complementary nonempty proper masks have equal Fin-valued means. -/
theorem maskMeanIndex_complement (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (hnA : NonemptyMask A) (hC : Proper (fun i => !(A i)))
    (hnC : NonemptyMask (fun i => !(A i))) :
    maskMeanIndex P (fun i => !(A i)) hC hnC = maskMeanIndex P A hA hnA := by
  apply Fin.ext
  change zA P.p (extendMask (fun i => !(A i))) = zA P.p (extendMask A)
  have he : zA P.p (extendMask (fun i => !(A i))) =
      zA P.p (MeanObstruction.complement (extendMask A)) := by
    apply mean_congr_support
    intro i hi
    simp [extendMask, MeanObstruction.complement, hi]
  exact he.trans (MeanObstruction.mean_complement P.prime P.odd (extendMask A)
    (extend_nonempty_proper A hnA hA))

/-- Complementary pulled-back roles preserve zero origin without an
inductive hypothesis: both means are defined and equal. -/
theorem outer_relative_zero_complement (P : Parameters) (e : Pose P.p)
    (he : e.AffineIndex) (A B : Mask P.p) (hA : Proper A) (hB : Proper B)
    (hAB : ∀ i, B (e.frame.perm i) = !(A i)) :
    ((arithmeticChild P (.outer A hA)).relative (refine P e (.outer B hB))).ZeroOrigin P := by
  have hnA : NonemptyMask A := by
    obtain ⟨j, hj⟩ := hB
    refine ⟨e.frame.inverse j, ?_⟩
    have hi := hAB (e.frame.inverse j)
    rw [e.frame.right_inverse, hj] at hi
    cases ha : A (e.frame.inverse j) <;> simp [ha] at hi ⊢
  have hnB : NonemptyMask B := by
    obtain ⟨i, hi⟩ := hA
    exact ⟨e.frame.perm i, by rw [hAB i, hi]; rfl⟩
  have hC : Proper (fun i => !(A i)) := by
    obtain ⟨i, hi⟩ := hnA
    exact ⟨i, by simp [hi]⟩
  have hnC : NonemptyMask (fun i => !(A i)) := by
    obtain ⟨i, hi⟩ := hA
    exact ⟨i, by simp [hi]⟩
  have hm := affine_mask_mean_index P e.frame he (fun i => !(A i)) B hC hnC hB hnB hAB
  rw [maskMeanIndex_complement P A hA hnA hC hnC] at hm
  exact outer_relative_zero_of_mean P e A B hA hnA hB hnB hm

theorem Pose.Same.zero_origin (P : Parameters) {q r : Pose P.p} (h : q.Same r)
    (hq : q.ZeroOrigin P) : r.ZeroOrigin P := by
  change r.frame.perm (zeroIndex P) = zeroIndex P
  rw [← h.1 (zeroIndex P)]
  exact hq

/-- The depth induction is over actual finite supertiles. Its only recursive
case is the empty--empty negative singleton wall from the geometric reduction. -/
theorem finite_equal_anchor_contact_zero_origin (P : Parameters) (n : Nat)
    (q r : Pose P.p) (hq : Descendant P n (identityPose P.p) q)
    (hr : Descendant P n (identityPose P.p) r) (hc : FaceContact q r)
    (h : q.anchor = r.anchor) : (q.relative r).ZeroOrigin P := by
  induction n generalizing q r with
  | zero =>
    have he : q = r := hq.eq.symm.trans hr.eq
    subst r
    obtain ⟨hd, x, y, hx, _, _⟩ := hc
    exact False.elim (hd x ⟨hx, hx⟩)
  | succ n ih =>
    obtain ⟨Q, a, hQ, hQa⟩ := (descendant_succ_iff P n (identityPose P.p) q).mp hq
    obtain ⟨R, b, hR, hRb⟩ := (descendant_succ_iff P n (identityPose P.p) r).mp hr
    have hqe := hQa.eq
    have hre := hRb.eq
    subst q
    subst r
    have hparent := finite_equal_anchor_contact_parents P n (identityPose P.p)
      Q R hQ hR a b hc h
    obtain ⟨A, hA, B, hB, rfl, rfl, hE, _, hroles⟩ :=
      generated_equal_anchor_contact_parent_data P n Q R hQ hR a b hc h
    have haff := generated_contact_affine_index P (Q.relative R) hE
    rw [refine_relative]
    rcases hroles with ⟨hAB, hempty⟩ | hAB
    · apply outer_relative_zero_equal P (Q.relative R) haff A B hA hB hAB
      intro hA0
      exact ih Q R hQ hR hparent ((relative_anchor_zero_iff Q R).mp (hempty hA0))
    · exact outer_relative_zero_complement P (Q.relative R) haff A B hA hB hAB

/-- Every actual generated contact at zero anchor fixes coordinate index 0.
No enumerated catalog, coarse closure, full-world extension, or primitive-g
assumption occurs in the statement or proof. -/
theorem generated_contact_zero_origin (P : Parameters) (e : Pose P.p)
    (he : GeneratedContact P e) (hz : ∀ i, e.anchor i = 0) : e.ZeroOrigin P := by
  obtain ⟨n, q, r, hq, hr, hc, hs⟩ := he
  have hz' : ∀ i, (q.relative r).anchor i = 0 := by
    intro i
    rw [hs.2.2 i]
    exact hz i
  exact hs.zero_origin P (finite_equal_anchor_contact_zero_origin P n q r hq hr hc
    ((relative_anchor_zero_iff q r).mp hz'))

end RegisteredPrime
