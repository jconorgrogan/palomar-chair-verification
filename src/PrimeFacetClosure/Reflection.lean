module
public import PrimeFacetClosure.MinusAffine
public import PrimeFacetClosure.Transport
public import closure_analysis.CoarseWalls
@[expose] public section
namespace RegisteredPrime.PrimeFacetClosure
open Uniform

/-- The literal coordinate involution i ↦ -i over F_p. -/
def negIndex (P : Parameters) (i : Fin P.p) : Fin P.p :=
  ⟨(P.p - i.val) % P.p, Nat.mod_lt _ (by have := P.prime.two_le; omega)⟩

theorem negIndex_congr (P : Parameters) (i : Fin P.p) :
    MEq P.p (negIndex P i).val (-(i.val : Int)) := by
  have h := MEq.emod_self (p := P.p) ((P.p : Int) - i.val)
  have he : ((P.p - i.val : Nat) : Int) = (P.p : Int) - i.val := by omega
  change MEq P.p (((P.p - i.val) % P.p : Nat) : Int) _
  rw [Int.natCast_emod, he]
  exact h.trans ((MEq.zero_of_dvd (Int.dvd_refl (P.p : Int))).sub
    (MEq.refl (i.val : Int)) |>.trans (MEq.of_eq (by omega)))

theorem negIndex_involutive (P : Parameters) (i : Fin P.p) :
    negIndex P (negIndex P i) = i := by
  have ht : MEq P.p (-(negIndex P i).val : Int) (i.val : Int) := by
    simpa using (MEq.refl (-1 : Int)).mul (negIndex_congr P i)
  have h := (negIndex_congr P (negIndex P i)).trans ht
  apply Fin.ext
  have hlt := (negIndex P (negIndex P i)).isLt
  have he := h.eq_of_lt (by omega) (by omega) (by omega) (by omega)
  omega

@[simp] theorem negIndex_zero (P : Parameters) : negIndex P (zeroIndex P) = zeroIndex P := by
  apply Fin.ext
  simp [negIndex, zeroIndex]

def reflectionFrame (P : Parameters) : RegisteredFrame P.p where
  perm := negIndex P
  inverse := negIndex P
  left_inverse := negIndex_involutive P
  right_inverse := negIndex_involutive P
  negative := fun _ => false

theorem reflectionFrame_affine (P : Parameters) : (reflectionFrame P).AffineIndex := by
  refine ⟨P.p-1, 0, IsPrime.not_dvd_of_pos_lt (by have := P.prime.two_le; omega)
    (by have := P.prime.two_le; omega), fun i => ?_⟩
  have hg : MEq P.p ((P.p-1 : Nat) : Int) (-1) := by
    refine ⟨1, ?_⟩
    have := P.prime.two_le
    omega
  have ht : MEq P.p (-(i.val : Int)) (((P.p-1 : Nat) : Int) * i.val + 0) := by
    simpa using (hg.mul (MEq.refl (i.val : Int))).symm
  exact (negIndex_congr P i).trans ht

/-- A centered signed-affine permutation is exactly identity or negation. -/
theorem signedAffine_zero_dichotomy (P : Parameters) (F : RegisteredFrame P.p)
    (ha : SignedAffine F) (hz : F.perm (zeroIndex P) = zeroIndex P) :
    (∀ i, F.perm i = i) ∨ (∀ i, F.perm i = negIndex P i) := by
  obtain ⟨s, hs, b, hf⟩ := ha
  have hb := hf (zeroIndex P)
  rw [hz] at hb
  have hb' : MEq P.p b 0 := by simpa [zeroIndex] using hb.symm
  have hm (i : Fin P.p) : MEq P.p (F.perm i).val (s * i.val) :=
    (hf i).trans (((MEq.refl (s * (i.val : Int))).add hb').trans
      (MEq.of_eq (by simp)))
  rcases hs with rfl | rfl
  · left
    intro i
    have hh : MEq P.p (F.perm i).val i.val := by simpa using hm i
    apply Fin.ext
    have hi := (F.perm i).isLt
    have he := hh.eq_of_lt (by omega) (by omega) (by omega) (by omega)
    omega
  · right
    intro i
    have hmi : MEq P.p (F.perm i).val (-(i.val : Int)) := by simpa using hm i
    have hh := hmi.trans ((negIndex_congr P i).symm)
    apply Fin.ext
    have hi := (F.perm i).isLt
    have hj := (negIndex P i).isLt
    have he := hh.eq_of_lt (by omega) (by omega) (by omega) (by omega)
    omega

/-- A proper frame with a single negative row cannot have identity permutation. -/
theorem singleton_proper_not_identity {p : Nat} (F : RegisteredFrame p) (j : Fin p)
    (hp : F.IsProper) (hn : ∀ i, F.negative i = decide (i=j)) :
    ¬ (∀ i, F.perm i = i) := by
  intro hi
  have hperm : F.toUniform.perm = fun i => i := by
    funext i
    by_cases h : i < p <;> simp [RegisteredFrame.toUniform, h, hi]
  have hcard : negCount p F.toUniform.neg = 1 := by
    change suppCard p F.toUniform.neg = 1
    rw [show suppCard p F.toUniform.neg = suppCard p (MeanObstruction.singleton j.val) from
      MeanObstruction.card_congr (fun i h => by
        simp [RegisteredFrame.toUniform, extendMask, h, hn, MeanObstruction.singleton,
          Fin.ext_iff])]
    exact MeanObstruction.card_singleton j.isLt
  have h := rotation_parity hp
  rw [hperm, invCount_id, hcard] at h
  contradiction

/-- The exact gauged bridge follows from actual properness, centering, and
signed-affine index control, rather than an assumed bridge catalogue. -/
theorem centered_singleton_eq_bridge (P : Parameters) (F : RegisteredFrame P.p)
    (j : Fin P.p) (ha : SignedAffine F) (hz : F.perm (zeroIndex P)=zeroIndex P)
    (hp : F.IsProper) (hn : ∀ i, F.negative i=decide (i = j)) :
    F = bridge (reflectionFrame P) j := by
  rcases signedAffine_zero_dichotomy P F ha hz with hid | hneg
  · exact False.elim (singleton_proper_not_identity F j hp hn hid)
  · apply RegisteredFrame.ext_data
    · exact funext hneg
    · exact funext hn

/-- The actual shared wall role equations force a singleton sign in the
normalized child frame at its transported normal axis. -/
theorem wall_child_singleton (P : Parameters) (e : Pose P.p) (j : Fin P.p)
    (A B : Mask P.p) (hA : Proper A) (hB : Proper B)
    (hab : ∀ i, B (e.frame.perm i)=xor (A i) (wallDiscrepancy e j i)) :
    ∀ i, ((arithmeticChild P (.outer A hA)).relative
      (refine P e (.outer B hB))).frame.negative i =
      decide (i=(arithmeticChild P (.outer A hA)).frame.perm j) := by
  intro i
  rw [relative_negative, refine_outer_negative, child_outer_negative, hab]
  let x := (arithmeticChild P (.outer A hA)).frame.inverse i
  have he : i = (arithmeticChild P (.outer A hA)).frame.perm j ↔ x=j := by
    constructor
    · intro h
      simpa only [x, (arithmeticChild P (.outer A hA)).frame.left_inverse] using
        congrArg (arithmeticChild P (.outer A hA)).frame.inverse h
    · intro h
      have hh := congrArg (arithmeticChild P (.outer A hA)).frame.perm h
      simpa only [x, (arithmeticChild P (.outer A hA)).frame.right_inverse] using hh
  simp only [he]
  change xor (A x) (xor (e.frame.negative x)
    (xor (A x) (xor (e.frame.negative x) (decide (x = j))))) = decide (x = j)
  cases A x <;> cases e.frame.negative x <;> cases decide (x = j) <;> rfl

/-- Every actual generated wall edge has the source's exact gauged transport
L_k. All graph-generator arithmetic is derived from generated E, never supplied
as a catalogue or closure assumption. -/
theorem generated_wall_gauge_bridge (P : Parameters) (hm : P.mu=1)
    (hg : P.g=P.p-1) (e : Pose P.p) (he : GeneratedContact P e)
    (j : Fin P.p) (side : Bool) (hbox : boxLower e=wallBox j side)
    (A B : Mask P.p) (hA : Proper A) (hB : Proper B) (hAj : A j=side)
    (hab : ∀ i, B (e.frame.perm i)=xor (A i) (wallDiscrepancy e j i)) :
    ((arithmeticChild P (.outer A hA)).relative
      (refine P e (.outer B hB))).frame =
      bridge (reflectionFrame P) ((arithmeticChild P (.outer A hA)).frame.perm j) := by
  let q := (arithmeticChild P (.outer A hA)).relative (refine P e (.outer B hB))
  have hc := refined_outer_contact_of_adjacent_cells P (identityPose P.p) e A B hA hB
    (by simpa only [identity_cell] using wall_matching_cells_adjacent P e j side hbox A B hAj hab)
  rw [(identity_refine_same P (.outer A hA)).eq] at hc
  have hgen : GeneratedContact P q := generated_refinement_contact P e he _ _ hc
  have hz : ∀ i, q.anchor i=0 := (relative_anchor_zero_iff _ _).mpr
    (wall_matching_outer_anchors P e j side hbox A B hA hB hAj hab)
  exact centered_singleton_eq_bridge P q.frame _
    (generated_signedAffine P hm hg q hgen)
    (generated_contact_zero_origin P q hgen hz)
    (generated_frame_proper P q hgen)
    (wall_child_singleton P e j A B hA hB hab)

#print axioms signedAffine_zero_dichotomy
#print axioms centered_singleton_eq_bridge
#print axioms generated_wall_gauge_bridge
end RegisteredPrime.PrimeFacetClosure
