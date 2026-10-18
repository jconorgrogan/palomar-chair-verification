module
public import RegisteredPrime.WorldExistence
public import closure_analysis.ZeroOrigin
@[expose] public section
namespace RegisteredPrime
open Uniform

theorem uniformFrame_ext_data (F G : Frame) (hp : F.perm = G.perm)
    (hn : F.neg = G.neg) : F = G := by
  cases F
  cases G
  cases hp
  cases hn
  rfl

/-- The bounded Nat-frame representation respects full frame composition. -/
theorem RegisteredFrame.toUniform_comp {p : Nat} (F G : RegisteredFrame p) :
    (F.comp G).toUniform = F.toUniform.comp G.toUniform := by
  apply uniformFrame_ext_data
  · funext i
    by_cases hi : i < p
    · simp [RegisteredFrame.toUniform, RegisteredFrame.comp, Frame.comp, hi,
        (F.perm ⟨i, hi⟩).isLt]
    · simp [RegisteredFrame.toUniform, RegisteredFrame.comp, Frame.comp, hi]
  · funext i
    by_cases hi : i < p
    · simp [RegisteredFrame.toUniform, RegisteredFrame.comp, Frame.comp, extendMask, hi,
        (F.perm ⟨i, hi⟩).isLt]
    · simp [RegisteredFrame.toUniform, RegisteredFrame.comp, Frame.comp, extendMask, hi]

theorem RegisteredFrame.toUniform_identity (p : Nat) :
    (identityPose p).frame.toUniform = Frame.id := by
  apply uniformFrame_ext_data
  · funext i
    by_cases hi : i < p <;> simp [RegisteredFrame.toUniform, identityPose, Frame.id]
  · funext i
    by_cases hi : i < p <;>
      simp [RegisteredFrame.toUniform, identityPose, Frame.id, extendMask, hi]

theorem RegisteredFrame.comp_inv_identity {p : Nat} (F : RegisteredFrame p) :
    F.comp F.inv = (identityPose p).frame := by
  apply RegisteredFrame.ext_data
  · funext i
    simp [RegisteredFrame.comp, RegisteredFrame.inv, identityPose, F.left_inverse]
  · funext i
    simp [RegisteredFrame.comp, RegisteredFrame.inv, identityPose, F.left_inverse]

theorem RegisteredFrame.IsProper.comp {p : Nat} {F G : RegisteredFrame p}
    (hF : F.IsProper) (hG : G.IsProper) : (F.comp G).IsProper := by
  change IsRotation p (F.comp G).toUniform
  rw [RegisteredFrame.toUniform_comp]
  exact IsRotation.comp hF hG

/-- Inversion preserves determinant +1, proved from the checked sign parity
composition theorem and the literal identity F·F⁻¹. -/
theorem RegisteredFrame.IsProper.inv {p : Nat} {F : RegisteredFrame p}
    (hF : F.IsProper) : F.inv.IsProper := by
  change IsRotation p F.toUniform at hF
  change IsRotation p F.inv.toUniform
  have hprod : F.toUniform.comp F.inv.toUniform = Frame.id := by
    rw [← RegisteredFrame.toUniform_comp, RegisteredFrame.comp_inv_identity,
      RegisteredFrame.toUniform_identity]
  have hrot : IsRotation p (F.toUniform.comp F.inv.toUniform) := by
    rw [hprod]
    exact IsRotation.id p
  have hp := rotation_parity hrot
  rw [negCount_comp p F.toUniform F.inv.toUniform F.toUniform_isPerm] at hp
  change (negCount p F.toUniform.neg + negCount p F.inv.toUniform.neg) % 2 =
    invCount p (fun i => F.inv.toUniform.perm (F.toUniform.perm i)) % 2 at hp
  rw [invCount_comp F.inv.toUniform_isPerm F.toUniform_isPerm] at hp
  have hfp := rotation_parity hF
  apply rotation_of_parity F.inv.toUniform_isPerm
  omega

theorem identity_frame_proper (p : Nat) : (identityPose p).frame.IsProper := by
  change IsRotation p (identityPose p).frame.toUniform
  rw [RegisteredFrame.toUniform_identity]
  exact IsRotation.id p

theorem refine_frame_proper (P : Parameters) (q : Pose P.p) (a : Role P.p)
    (hq : q.frame.IsProper) : (refine P q a).frame.IsProper :=
  RegisteredFrame.IsProper.comp hq (arithmeticChild_proper P a)

/-- Every actual finite arithmetic descendant retains proper orientation. -/
theorem descendant_frame_proper (P : Parameters) (n : Nat) (q t : Pose P.p)
    (hq : q.frame.IsProper) (ht : Descendant P n q t) : t.frame.IsProper := by
  induction n generalizing q with
  | zero => rw [← ht.eq]; exact hq
  | succ n ih =>
    obtain ⟨a, ha⟩ := ht
    exact ih (refine P q a) (refine_frame_proper P q a hq) ha

namespace WorldExistence

theorem interiorCopy_proper (P : Parameters) : (interiorCopy P).frame.IsProper :=
  descendant_frame_proper P 2 (identityPose P.p) (interiorCopy P)
    (identity_frame_proper P.p) (interiorCopy_descendant P)

theorem stageOrigin_proper (P : Parameters) (k : Nat) : (stageOrigin P k).frame.IsProper := by
  induction k with
  | zero => exact identity_frame_proper P.p
  | succ k ih =>
    have hs : (scalePose (2 * k) (interiorCopy P)).frame.IsProper := by
      rw [scalePose_frame]
      exact interiorCopy_proper P
    exact RegisteredFrame.IsProper.comp ih hs.inv

/-- Properness is a conclusion for every tile of the constructed world. -/
theorem world_proper (P : Parameters) : (world P).Proper := by
  intro q hq
  obtain ⟨k, d, hd, rfl⟩ := hq
  exact RegisteredFrame.IsProper.comp (stageOrigin_proper P k)
    (descendant_frame_proper P (2 * k) (identityPose P.p) d (identity_frame_proper P.p) hd)

end WorldExistence

/-- Rotation-only existence in the actual generated E language. -/
theorem registered_proper_E_world_exists (P : Parameters) :
    ∃ W : RegisteredWorld P.p, W.Legal P ∧ W.Proper :=
  ⟨WorldExistence.world P, WorldExistence.world_legal P, WorldExistence.world_proper P⟩

end RegisteredPrime
