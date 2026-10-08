module

public import SparseMonotiles.PyramidIsometryRigidity
public import SparseMonotiles.KeyCovariance

@[expose] public section

/-!
# From a trivial key stabilizer to an exact signed integer relative pose

The isometry whose registration is concluded below is arbitrary. The only
rigidity premise is the trivial stabilizer of the one fixed reference solid;
no signed-permutation assumption is imposed on that isometry.
-/
namespace SparseMonotiles

/-- Canonical images of a rigid metric set determine the full intervening isometry. -/
theorem isometryEquiv_eq_of_coincident_rigid_images {X : Type*} [MetricSpace X]
    (K : Set X) (hrigid : ∀ e : X ≃ᵢ X, e '' K = K → e = IsometryEquiv.refl X)
    (p q g : X ≃ᵢ X) (hg : g '' (p '' K) = q '' K) :
    g = p.symm.trans q := by
  let e := (p.trans g).trans q.symm
  have heK : e '' K = K := by
    calc
      e '' K = q.symm '' (g '' (p '' K)) := by
        rw [Set.image_image, Set.image_image]
        rfl
      _ = q.symm '' (q '' K) := by rw [hg]
      _ = K := by ext x; simp
  have he := hrigid e heK
  apply IsometryEquiv.ext
  intro x
  have hx := congrArg (fun f : X ≃ᵢ X => q (f (p.symm x))) he
  have hrefl (y : X) : (IsometryEquiv.refl X) y = y := rfl
  simpa [e, hrefl] using hx

namespace Canonical
open Contact

/-- The signed integer pose that carries canonical pose `p` to canonical pose `q`. -/
def relativeKeyPose {d : ℕ} (p q : Pose d) : Pose d where
  perm := q.perm.trans p.perm.symm
  negative := fun i => xor (q.negative i) (p.negative (p.perm.symm (q.perm i)))
  shift := fun i => q.shift i - q.sign i * p.sign (p.perm.symm (q.perm i)) *
    p.shift (p.perm.symm (q.perm i))

@[simp] theorem relativeKeyPose_sign {d : ℕ} (p q : Pose d) (i : Fin d) :
    (relativeKeyPose p q).sign i = q.sign i * p.sign (p.perm.symm (q.perm i)) := by
  cases hq : q.negative i <;> cases hp : p.negative (p.perm.symm (q.perm i)) <;>
    simp [relativeKeyPose, Pose.sign, hq, hp]

/-- The integer relative-pose formula agrees with physical Euclidean composition. -/
theorem relativeKeyPose_euclidean_apply {d : ℕ} (p q : Pose d) (x : Point d) :
    (relativeKeyPose p q).euclidean (p.euclidean x) = q.euclidean x := by
  ext i
  simp only [Pose.euclidean_apply, relativeKeyPose_sign, Int.cast_mul,
    relativeKeyPose, Equiv.trans_apply, Equiv.apply_symm_apply, Int.cast_sub]
  have hperm : p.perm ((Equiv.symm p.perm) (q.perm i)) = q.perm i :=
    p.perm.apply_symm_apply (q.perm i)
  cases hp : p.negative (p.perm.symm (q.perm i)) <;>
    cases hq : q.negative i <;> simp [Pose.sign, hp, hq, hperm] <;> ring

theorem relativeKeyPose_euclidean {d : ℕ} (p q : Pose d) :
    (relativeKeyPose p q).euclidean.toIsometryEquiv =
      p.euclidean.toIsometryEquiv.symm.trans q.euclidean.toIsometryEquiv := by
  apply IsometryEquiv.ext
  intro x
  simpa using relativeKeyPose_euclidean_apply p q (p.euclidean.symm x)

/-- Whole-key coincidence forces the intended signed integer pose whenever the
reference key's arbitrary-isometry stabilizer is trivial. -/
theorem arbitrary_isometry_eq_relativeKeyPose {d : ℕ} (K : Set (Point d))
    (hrigid : ∀ e : Point d ≃ᵢ Point d, e '' K = K → e = IsometryEquiv.refl (Point d))
    (p q : Pose d) (g : Point d ≃ᵢ Point d)
    (hg : g '' (p.euclidean '' K) = q.euclidean '' K) :
    g = (relativeKeyPose p q).euclidean.toIsometryEquiv := by
  rw [relativeKeyPose_euclidean]
  exact isometryEquiv_eq_of_coincident_rigid_images K hrigid
    p.euclidean.toIsometryEquiv q.euclidean.toIsometryEquiv g hg

#print axioms relativeKeyPose_euclidean
#print axioms arbitrary_isometry_eq_relativeKeyPose

end Canonical
end SparseMonotiles
