module

public import ProductClosure.NativeProfileDefinitions
public import PhysicalRegistration.PoseRealization

@[expose] public section

/-! Exact actual-isometry group laws for registered finite-polycube placement. -/
namespace ProductClosure.NativeCompiler
open PhysicalRegistration.NativeChair
noncomputable section
variable {m : ℕ}

@[simp] theorem poseIsometry_inv  (q : RegisteredPrime.Pose (m+1)) :
    poseIsometry q.inv = (poseIsometry q).symm := by
  apply IsometryEquiv.ext
  intro x
  apply (poseIsometry q).injective
  have h := congrArg (fun e : Space m ≃ᵢ Space m => e x) (poseIsometry_comp q q.inv)
  rw [RegisteredPrime.Pose.comp_inv, poseIsometry_identity] at h
  change x = poseIsometry q (poseIsometry q.inv x) at h
  simpa only [IsometryEquiv.apply_symm_apply] using h.symm

/-- The old row-pose relative operation is the literal relative isometry. -/
theorem poseIsometry_relative  (q r : RegisteredPrime.Pose (m+1)) :
    poseIsometry (q.relative r) = relativePlacement (poseIsometry q) (poseIsometry r) := by
  rw [RegisteredPrime.Pose.relative, poseIsometry_comp, poseIsometry_inv]
  rfl

end
end ProductClosure.NativeCompiler
