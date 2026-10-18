module

public import ProductClosure.ProductWorldBlockPose
public import ProductClosure.ProductGraphRightPlacements

@[expose] public section

/-! The graph worker's actual unrestricted Euclidean block lifts coincide
with the explicit original registered block poses, with canonical dimension
casts. These are full isometry equalities, not just cell-set equalities. -/
namespace ProductClosure.World
noncomputable section

open ProductGraphSites ProductGraphRightSites ProductGraphPlacements ProductGraphRightPlacements

/-- Full registered pose of an active-left generator and identity passive pose. -/
def nativeLeftPose {a : ℕ} (b : ℕ) (q : RegisteredPrime.Pose (a + 1)) :
    RegisteredPrime.Pose ((a + b) + 1) :=
  castPose (productDim a b) (blockPose q (RegisteredPrime.identityPose b))

/-- Full registered pose of an active-right generator and identity passive pose. -/
def nativeRightPose {a : ℕ} (b : ℕ) (q : RegisteredPrime.Pose (a + 1)) :
    RegisteredPrime.Pose ((a + b) + 1) :=
  castPose (rightProductDim a b) (blockPose (RegisteredPrime.identityPose b) q)

@[simp] theorem nativeLeftPose_apply_append {a b : ℕ}
    (q : RegisteredPrime.Pose (a + 1)) (x : Polycube.Space (a + 1)) (y : Polycube.Space b) :
    PhysicalRegistration.NativeChair.poseIsometry (nativeLeftPose b q) (appendNative x y) =
      appendNative (PhysicalRegistration.NativeChair.poseIsometry q x) y := by
  ext k
  obtain ⟨j, rfl⟩ := (ambientEquiv a b).surjective k
  cases j with
  | inl i =>
    rw [PhysicalRegistration.NativeChair.poseIsometry_apply, appendNative_left,
      PhysicalRegistration.NativeChair.poseIsometry_apply]
    simp [nativeLeftPose, ambientEquiv, RegisteredPrime.RegisteredFrame.sign,
      blockPose, blockFrame, appendNative, Polycube.appendPoint]
  | inr i =>
    rw [PhysicalRegistration.NativeChair.poseIsometry_apply, appendNative_right]
    simp [nativeLeftPose, ambientEquiv, RegisteredPrime.RegisteredFrame.sign,
      blockPose, blockFrame, RegisteredPrime.identityPose, appendNative, Polycube.appendPoint]

@[simp] theorem nativeRightPose_apply_append {a b : ℕ}
    (q : RegisteredPrime.Pose (a + 1)) (x : Polycube.Space (a + 1)) (y : Polycube.Space b) :
    PhysicalRegistration.NativeChair.poseIsometry (nativeRightPose b q) (appendRightNative x y) =
      appendRightNative (PhysicalRegistration.NativeChair.poseIsometry q x) y := by
  ext k
  obtain ⟨j, rfl⟩ := (rightAmbientEquiv a b).surjective k
  cases j with
  | inl i =>
    rw [PhysicalRegistration.NativeChair.poseIsometry_apply, appendRightNative_left,
      PhysicalRegistration.NativeChair.poseIsometry_apply]
    simp [nativeRightPose, rightAmbientEquiv, RegisteredPrime.RegisteredFrame.sign,
      blockPose, blockFrame, appendRightNative, Polycube.appendPoint]
  | inr i =>
    rw [PhysicalRegistration.NativeChair.poseIsometry_apply, appendRightNative_right]
    simp [nativeRightPose, rightAmbientEquiv, RegisteredPrime.RegisteredFrame.sign,
      blockPose, blockFrame, RegisteredPrime.identityPose, appendRightNative, Polycube.appendPoint]

/-- Exact bridge from the actual geometric left block lift to the existing
registered-pose representation, including every signed frame entry. -/
theorem poseIsometry_nativeLeftPose {a b : ℕ} (q : RegisteredPrime.Pose (a + 1)) :
    PhysicalRegistration.NativeChair.poseIsometry (nativeLeftPose b q) =
      liftLeft (b := b) (PhysicalRegistration.NativeChair.poseIsometry q) := by
  apply IsometryEquiv.ext
  intro z
  let p := WithLp.ofLp (splitNative a b z)
  have hz : appendNative p.1 p.2 = z := by
    rw [← splitNative_symm_pair]
    exact (splitNative a b).symm_apply_apply z
  rw [← hz, nativeLeftPose_apply_append, liftLeft_append]

/-- Exact bridge for the actual geometric right block lift. -/
theorem poseIsometry_nativeRightPose {a b : ℕ} (q : RegisteredPrime.Pose (a + 1)) :
    PhysicalRegistration.NativeChair.poseIsometry (nativeRightPose b q) =
      liftRight (b := b) (PhysicalRegistration.NativeChair.poseIsometry q) := by
  apply IsometryEquiv.ext
  intro z
  let p := WithLp.ofLp (splitRightNative a b z)
  have hz : appendRightNative p.1 p.2 = z := by
    rw [← splitRightNative_symm_pair]
    exact (splitRightNative a b).symm_apply_apply z
  rw [← hz, nativeRightPose_apply_append, liftRight_append]

#print axioms poseIsometry_nativeLeftPose
#print axioms poseIsometry_nativeRightPose

end
end ProductClosure.World
