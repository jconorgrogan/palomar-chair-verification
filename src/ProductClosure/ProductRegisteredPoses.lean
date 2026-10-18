module

public import ProductClosure.ProductWorldGraphPose
public import ProductClosure.ProductGraphSiteCoproduct
public import ProductClosure.IntegralPoseAlgebra
public import PhysicalRegistration.PoseRealization

@[expose] public section

/-! Exact registered-pose binding for the actual common-chart factor lifts. -/
namespace ProductClosure.ProductRegisteredPoses
noncomputable section
open NativeCompiler ProductGraphSites ProductGraphPlacements ProductGraphSiteCoproduct
open ProductGraphRightPlacements

@[simp] theorem registeredCast_trans {d e f : ℕ} (h : d = e) (k : e = f)
    (q : RegisteredPrime.Pose d) :
    World.castPose k (World.castPose h q) = World.castPose (h.trans k) q := by
  subst e
  subst f
  rfl

theorem registeredCast_injective {d e : ℕ} (h : d = e) :
    Function.Injective (World.castPose h) := by subst e; exact Function.injective_id

@[simp] theorem poseIsometry_castPose {m n : ℕ} (h : m = n) (q : RegisteredPrime.Pose (m+1)) :
    PhysicalRegistration.NativeChair.poseIsometry (World.castPose (congrArg (fun k => k+1) h) q) =
      poseCast h (PhysicalRegistration.NativeChair.poseIsometry q) := by subst n; rfl

/-- The right-factor lift is exactly the original block pose in the same
common native dimension used by the product compiler. -/
theorem poseIsometry_commonRightPose {a b : ℕ} (q : RegisteredPrime.Pose (b+1)) :
    PhysicalRegistration.NativeChair.poseIsometry
      (World.castPose (productDim a (b+1)) (World.blockPose (RegisteredPrime.identityPose (a+1)) q)) =
      commonLiftRight (a := a) (PhysicalRegistration.NativeChair.poseIsometry q) := by
  have he : World.castPose (productDim a (b+1))
      (World.blockPose (RegisteredPrime.identityPose (a+1)) q) =
      World.castPose (congrArg (fun k => k+1) (tangentSwap a b)) (World.nativeRightPose (a+1) q) := by
    unfold World.nativeRightPose
    rw [registeredCast_trans]
  rw [he, poseIsometry_castPose, World.poseIsometry_nativeRightPose]
  rfl

/-- A literal complete native contact forces an actual registered factor
pose. The Euclidean isometry equality is exact, not just an occupancy match. -/
theorem registeredPose_of_siteTransport {m : ℕ}
    {S : Finset (Polycube.LatticeIndex (m+1))} (g : Space m ≃ᵢ Space m)
    (u v : Site S) (h : SiteTransport g u v) :
    ∃ q : RegisteredPrime.Pose (m+1), g = PhysicalRegistration.NativeChair.poseIsometry q := by
  have hg := relativePlacement_integral_signed_permutation u v (IsometryEquiv.refl _) g
    (by intro j; simpa only [placedNormal_refl] using h.1 j)
    (by simpa only [placedNormal_refl] using h.2.1) h.2.2.symm
  have he : relativePlacement (IsometryEquiv.refl (Space m)) g = g := by
    apply IsometryEquiv.ext
    intro x
    rfl
  rw [he] at hg
  obtain ⟨q,hq⟩ := PhysicalRegistration.NativeChair.exists_registeredPoseRealizes g
    (show PhysicalRegistration.NativeChair.HasIntegralSignedPermutation g from hg)
  exact ⟨q,hq.eq_poseIsometry⟩

/-- Identification with a left block lift recovers the entire original
registered pose, including its passive identity translation. -/
theorem registeredPose_eq_leftBlock {a b : ℕ}
    {SA : Finset (Polycube.LatticeIndex (a+1))}
    (q : RegisteredPrime.Pose ((a+1)+(b+1))) (g : Space a ≃ᵢ Space a)
    (u v : Site SA) (ht : SiteTransport g u v)
    (he : PhysicalRegistration.NativeChair.poseIsometry (World.castPose (productDim a (b+1)) q) =
      liftLeft (b := b+1) g) :
    ∃ qA : RegisteredPrime.Pose (a+1), g = PhysicalRegistration.NativeChair.poseIsometry qA ∧
      q = World.blockPose qA (RegisteredPrime.identityPose (b+1)) := by
  obtain ⟨qA,rfl⟩ := registeredPose_of_siteTransport g u v ht
  refine ⟨qA,rfl, ?_⟩
  apply registeredCast_injective (productDim a (b+1))
  apply PhysicalRegistration.NativeChair.poseIsometry_injective
  rw [he, ← World.poseIsometry_nativeLeftPose]
  rfl

/-- Symmetric right-block identification in the same ambient chart. -/
theorem registeredPose_eq_rightBlock {a b : ℕ}
    {SB : Finset (Polycube.LatticeIndex (b+1))}
    (q : RegisteredPrime.Pose ((a+1)+(b+1))) (g : Space b ≃ᵢ Space b)
    (u v : Site SB) (ht : SiteTransport g u v)
    (he : PhysicalRegistration.NativeChair.poseIsometry (World.castPose (productDim a (b+1)) q) =
      commonLiftRight (a := a) g) :
    ∃ qB : RegisteredPrime.Pose (b+1), g = PhysicalRegistration.NativeChair.poseIsometry qB ∧
      q = World.blockPose (RegisteredPrime.identityPose (a+1)) qB := by
  obtain ⟨qB,rfl⟩ := registeredPose_of_siteTransport g u v ht
  refine ⟨qB,rfl, ?_⟩
  apply registeredCast_injective (productDim a (b+1))
  apply PhysicalRegistration.NativeChair.poseIsometry_injective
  rw [he, poseIsometry_commonRightPose]

#print axioms poseIsometry_commonRightPose
#print axioms registeredPose_eq_leftBlock
#print axioms registeredPose_eq_rightBlock
end
end ProductClosure.ProductRegisteredPoses
