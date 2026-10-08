module
public import closure_analysis.ZeroOrigin
@[expose] public section
namespace RegisteredPrime
open Uniform

/-- A zero-origin fine contact forces equality of the two pulled-back means.
This is the direct input to the bounded-mask obstruction, with no explicit
slope/intercept or powers-of-g cancellation. -/
theorem outer_zero_origin_forces_mean_eq (P : Parameters) (e : Pose P.p)
    (he : e.AffineIndex) (A B C : Mask P.p)
    (hA : Proper A) (hnA : NonemptyMask A) (hB : Proper B)
    (hC : Proper C) (hnC : NonemptyMask C)
    (hBC : ∀ i, B (e.frame.perm i) = C i)
    (hz : ((arithmeticChild P (.outer A hA)).relative
      (refine P e (.outer B hB))).ZeroOrigin P) :
    zA P.p (extendMask A) = zA P.p (extendMask C) := by
  have hnB : NonemptyMask B := by
    obtain ⟨i, hi⟩ := hnC
    exact ⟨e.frame.perm i, (hBC i).trans hi⟩
  have hmC := affine_mask_mean_index P e.frame he C B hC hnC hB hnB hBC
  change (arithmeticChild P (.outer B hB)).frame.perm
    (e.frame.perm ((arithmeticChild P (.outer A hA)).frame.inverse (zeroIndex P))) =
      zeroIndex P at hz
  rw [outer_inverse_zero_mean P A hA hnA] at hz
  have hmA := congrArg (arithmeticChild P (.outer B hB)).frame.inverse hz
  rw [(arithmeticChild P (.outer B hB)).frame.left_inverse,
    outer_inverse_zero_mean P B hB hnB] at hmA
  have hAC := congrArg e.frame.inverse (hmA.trans hmC.symm)
  rw [e.frame.left_inverse, e.frame.left_inverse] at hAC
  exact congrArg Fin.val hAC

/-- Empty/empty refinement preserves and reflects the fixed-zero property.
This is the descent step for a coarse negative singleton wall. -/
theorem empty_relative_zero_origin_iff (P : Parameters) (e : Pose P.p) :
    ((arithmeticChild P (.outer (fun _ => false) (empty_proper P))).relative
      (refine P e (.outer (fun _ => false) (empty_proper P)))).ZeroOrigin P ↔
        e.ZeroOrigin P := by
  change ((arithmeticChild P (.outer (fun _ => false) (empty_proper P))).frame.perm
    (e.frame.perm
      ((arithmeticChild P (.outer (fun _ => false) (empty_proper P))).frame.inverse
        (zeroIndex P))) = zeroIndex P) ↔ e.frame.perm (zeroIndex P) = zeroIndex P
  rw [empty_child_frame, central_inverse_zero P]
  constructor
  · intro h
    have he := congrArg (arithmeticChild P .central).frame.inverse h
    rw [(arithmeticChild P .central).frame.left_inverse, central_inverse_zero P] at he
    exact he
  · intro h
    rw [h, central_index_zero P]

end RegisteredPrime
