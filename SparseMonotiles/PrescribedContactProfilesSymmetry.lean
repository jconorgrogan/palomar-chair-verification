module

public import SparseMonotiles.RegisteredIsometryGroup
public import SparseMonotiles.ContactIndexedChecker

@[expose] public section

/-! # Exact inverse-pose symmetry of shared oriented facets
The signed integer formulas retain both normal reversal and translation.
-/
namespace SparseMonotiles
open Contact CarrierHierarchy

theorem shared_inversePose {d : ℕ} {p : Pose d} {a b : Facet d}
    (h : Shared p a b) : Shared (inversePose p) b a := by
  have haxis : p.perm.symm b.axis=a.axis := by
    rw [← h.2.1,p.perm.symm_apply_apply]
  refine ⟨?_,haxis,?_⟩
  · funext j
    have hc := congrFun h.1 (p.perm.symm j)
    simp only [Pose.scaledPoint,Equiv.apply_symm_apply] at hc
    change b.centre2 j = (inversePose p).sign j*a.centre2 (p.perm.symm j)+
      2*(-p.sign (p.perm.symm j)*p.shift (p.perm.symm j))
    cases hn : p.negative (p.perm.symm j) <;>
      simp [inversePose,Pose.sign,hn] at hc ⊢ <;> omega
  · have hsign : (inversePose p).sign b.axis=p.sign a.axis := by
      simp [inversePose,Pose.sign,haxis]
    rw [hsign]
    have hn := h.2.2
    cases hb : p.negative a.axis <;> simp [Pose.sign,hb] at hn ⊢ <;> omega

theorem reverse_relative_isometry_pose {d : ℕ} (gA gB : Point d ≃ᵢ Point d)
    (p : Pose d) (hp : gB.trans gA.symm=p.euclidean.toIsometryEquiv) :
    gA.trans gB.symm=(inversePose p).euclidean.toIsometryEquiv := by
  rw [inversePose_euclidean]
  have h := congrArg (fun f : Point d ≃ᵢ Point d => f.symm) hp
  have he : (gB.trans gA.symm).symm = gA.trans gB.symm := by
    ext x
    simp [IsometryEquiv.symm_trans_apply]
  have hs : p.euclidean.toIsometryEquiv.symm = p.euclidean.symm.toIsometryEquiv := by
    ext x
    rfl
  simpa only [he,hs] using h

#print axioms shared_inversePose
#print axioms reverse_relative_isometry_pose
end SparseMonotiles
