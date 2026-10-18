module

public import ClarkSeed.HierarchyAdapter

@[expose] public section

/-! Faithful Euclidean realization, composition, inversion and exact geometric
cell footprints for the recovered poses. The scaled-key mating bit is excluded. -/
namespace ClarkSeed.PoseAdapter
noncomputable section
open SparseMonotiles

/-- The actual Euclidean action of the recovered pose. -/
def realization {m : ℕ} (p : Contact.Pose (m+1)) :
    PhysicalRegistration.NativeChair.Space m ≃ᵢ PhysicalRegistration.NativeChair.Space m :=
  PhysicalRegistration.NativeChair.poseIsometry (toRegistered p)

@[simp] theorem realization_apply {m : ℕ} (p : Contact.Pose (m+1))
    (x : PhysicalRegistration.NativeChair.Space m) (i : Fin (m+1)) :
    realization p x i = (p.sign i : ℝ) * x (p.perm i) + (p.shift i : ℝ) :=
  poseIsometry_apply p x i

theorem realization_injective {m : ℕ} : Function.Injective (@realization m) :=
  PhysicalRegistration.NativeChair.poseIsometry_injective.comp toRegistered_injective

@[simp] theorem realization_compose {m : ℕ} (p q : Contact.Pose (m+1)) :
    realization (CarrierHierarchy.compose p q) = (realization q).trans (realization p) := by
  unfold realization
  rw [toRegistered_compose, PhysicalRegistration.NativeChair.poseIsometry_comp]

@[simp] theorem realization_rootPose (m : ℕ) :
    realization (CarrierHierarchy.rootPose (m+1)) = IsometryEquiv.refl _ := by
  unfold realization
  rw [toRegistered_rootPose, PhysicalRegistration.NativeChair.poseIsometry_identity]

@[simp] theorem realization_inversePose {m : ℕ} (p : Contact.Pose (m+1)) :
    realization (CarrierHierarchy.inversePose p) = (realization p).symm := by
  have h := realization_compose p (CarrierHierarchy.inversePose p)
  rw [CarrierHierarchy.compose_inversePose, realization_rootPose] at h
  apply IsometryEquiv.ext
  intro x
  apply (realization p).injective
  have hx := congrArg (fun e : PhysicalRegistration.NativeChair.Space m ≃ᵢ
      PhysicalRegistration.NativeChair.Space m => e x) h
  change x = realization p (realization (CarrierHierarchy.inversePose p) x) at hx
  rw [IsometryEquiv.apply_symm_apply]
  exact hx.symm

@[simp] theorem realization_normalize {m : ℕ} (p q : Contact.Pose (m+1)) :
    realization (CarrierHierarchy.normalize p q) =
      (realization q).trans (realization p).symm := by
  rw [CarrierHierarchy.normalize, realization_compose, realization_inversePose]

/-- Exact image of each actual closed unit cube, including every negative
lower-corner correction. -/
theorem realization_image_latticeCell {m : ℕ} (p : Contact.Pose (m+1))
    (z : Contact.Cell (m+1)) :
    realization p '' ProductClosure.Polycube.latticeCell z =
      ProductClosure.Polycube.latticeCell (p.cell z) := by
  simpa only [realization, poseCellIndex_toRegistered] using
    ProductClosure.World.pose_image_latticeCell (toRegistered p) z

/-- Equality of the actual occupied bodies, not just a combinatorial cell
count or an abstract state action. -/
theorem realization_image_carrier {m : ℕ} (p : Contact.Pose (m+1))
    (S : Finset (Contact.Cell (m+1))) :
    realization p '' ProductClosure.Polycube.carrier S =
      ProductClosure.Polycube.carrier (S.image p.cell) := by
  have h := ProductClosure.World.placedCarrier_eq_carrier_image S (toRegistered p)
  have he : ProductClosure.World.poseCellIndex (toRegistered p) = p.cell :=
    funext (poseCellIndex_toRegistered p)
  rw [he] at h
  exact h

#print axioms realization_injective
#print axioms realization_inversePose
#print axioms realization_normalize
#print axioms realization_image_carrier
end
end ClarkSeed.PoseAdapter
