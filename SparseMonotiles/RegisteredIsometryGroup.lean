module

public import SparseMonotiles.KeyCovariance
public import SparseMonotiles.CarrierHierarchyCharts

@[expose] public section

/-! The exact finite pose encoding realizes a subgroup of the full Euclidean
isometry group. These identities propagate registered frames along matched-key
contacts without assuming global registration. -/
namespace SparseMonotiles.CarrierHierarchy
open Contact

theorem compose_euclidean {d : ℕ} (p q : Pose d) :
    (compose p q).euclidean = q.euclidean.trans p.euclidean := by
  apply DFunLike.ext
  intro x
  ext i
  change (compose p q).euclidean x i = p.euclidean (q.euclidean x) i
  rw [Pose.euclidean_apply,Pose.euclidean_apply,Pose.euclidean_apply,compose_sign]
  simp only [compose,Equiv.trans_apply,Int.cast_mul,Int.cast_add]
  ring

@[simp] theorem rootPose_euclidean {d : ℕ} :
    (rootPose d).euclidean = AffineIsometryEquiv.refl ℝ (Point d) := by
  apply DFunLike.ext
  intro x
  ext i
  simp [Pose.euclidean_apply,rootPose,Pose.sign]

theorem inversePose_euclidean {d : ℕ} (p : Pose d) :
    (inversePose p).euclidean = p.euclidean.symm := by
  apply DFunLike.ext
  intro x
  apply p.euclidean.injective
  have h := congrArg (fun f : Point d ≃ᵃⁱ[ℝ] Point d => f x)
    (compose_euclidean p (inversePose p))
  rw [compose_inversePose,rootPose_euclidean] at h
  change x = p.euclidean ((inversePose p).euclidean x) at h
  rw [p.euclidean.apply_symm_apply]
  exact h.symm

end CarrierHierarchy

namespace Contact
open CarrierHierarchy

def IsRegisteredIsometry {d : ℕ} (f : Point d ≃ᵢ Point d) : Prop :=
  ∃ p : Pose d, f=p.euclidean.toIsometryEquiv

theorem IsRegisteredIsometry.refl (d : ℕ) :
    IsRegisteredIsometry (IsometryEquiv.refl (Point d)) := by
  refine ⟨rootPose d,?_⟩
  rw [rootPose_euclidean]
  rfl

theorem IsRegisteredIsometry.trans {d : ℕ} {f g : Point d ≃ᵢ Point d}
    (hf : IsRegisteredIsometry f) (hg : IsRegisteredIsometry g) :
    IsRegisteredIsometry (f.trans g) := by
  obtain ⟨p,rfl⟩ := hf
  obtain ⟨q,rfl⟩ := hg
  refine ⟨compose q p,?_⟩
  rw [compose_euclidean]
  rfl

theorem IsRegisteredIsometry.symm {d : ℕ} {f : Point d ≃ᵢ Point d}
    (hf : IsRegisteredIsometry f) : IsRegisteredIsometry f.symm := by
  obtain ⟨p,rfl⟩ := hf
  refine ⟨inversePose p,?_⟩
  rw [inversePose_euclidean]
  rfl

/-- A registered local relative frame extends an already registered component. -/
theorem IsRegisteredIsometry.extend_relative {d : ℕ}
    (gA gB e : Point d ≃ᵢ Point d)
    (hA : IsRegisteredIsometry (gA.trans e))
    (hBA : IsRegisteredIsometry (gB.trans gA.symm)) :
    IsRegisteredIsometry (gB.trans e) := by
  have h := hBA.trans hA
  have heq : (gB.trans gA.symm).trans (gA.trans e) = gB.trans e := by
    ext x
    simp
  simpa only [heq] using h

#print axioms IsRegisteredIsometry.trans
#print axioms IsRegisteredIsometry.symm
#print axioms IsRegisteredIsometry.extend_relative
end Contact
end SparseMonotiles
