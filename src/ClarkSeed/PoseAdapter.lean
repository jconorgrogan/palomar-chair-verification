module

public import SparseMonotiles.ContactChecker
public import ProductClosure.ProductWorldPlaced
public import AtlasPeriods.Translation

@[expose] public section

/-! Exact signed-output-row identification of recovered CLARK poses with the
current native registered poses. These are spatial actions only; the separate
`Contact.Pose.key` mating action flips its bump bit and is not a group action. -/
namespace ClarkSeed.PoseAdapter
noncomputable section
open SparseMonotiles

/-- Preserve the full frame and affine anchor, not merely the occupied set. -/
def toRegistered {d : ℕ} (p : Contact.Pose d) : RegisteredPrime.Pose d where
  frame := {
    perm := p.perm
    inverse := p.perm.symm
    left_inverse := p.perm.symm_apply_apply
    right_inverse := p.perm.apply_symm_apply
    negative := p.negative }
  anchor := p.shift

/-- The inverse identification retains the signed-output-row convention. -/
def toContact {d : ℕ} (p : RegisteredPrime.Pose d) : Contact.Pose d where
  perm := {
    toFun := p.frame.perm
    invFun := p.frame.inverse
    left_inv := p.frame.left_inverse
    right_inv := p.frame.right_inverse }
  negative := p.frame.negative
  shift := p.anchor

@[simp] theorem toContact_toRegistered {d : ℕ} (p : Contact.Pose d) :
    toContact (toRegistered p) = p := by
  cases p
  rfl

@[simp] theorem toRegistered_toContact {d : ℕ} (p : RegisteredPrime.Pose d) :
    toRegistered (toContact p) = p := by
  apply RegisteredPrime.Pose.Same.eq
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- A genuine equivalence of full placed states, with no gauge quotient. -/
def poseEquiv (d : ℕ) : Contact.Pose d ≃ RegisteredPrime.Pose d where
  toFun := toRegistered
  invFun := toContact
  left_inv := toContact_toRegistered
  right_inv := toRegistered_toContact

theorem toRegistered_injective {d : ℕ} : Function.Injective (@toRegistered d) :=
  (poseEquiv d).injective

theorem toContact_injective {d : ℕ} : Function.Injective (@toContact d) :=
  (poseEquiv d).symm.injective

@[simp] theorem sign_toRegistered {d : ℕ} (p : Contact.Pose d) (i : Fin d) :
    (toRegistered p).frame.sign i = p.sign i := rfl

/-- The negative-row lower-corner correction is exactly the old one. -/
@[simp] theorem cell_toRegistered {d : ℕ} (p : Contact.Pose d) (z : Contact.Cell d) :
    (toRegistered p).cell z = p.cell z := by
  funext i
  change (p.shift i + p.sign i * z (p.perm i)) - (if p.negative i then 1 else 0) =
    (p.sign i * z (p.perm i) + p.shift i) - (if p.negative i then 1 else 0)
  rw [add_comm (p.shift i)]

/-- Equality to the actual finite-polycube occupied-cell action. -/
@[simp] theorem poseCellIndex_toRegistered {d : ℕ} (p : Contact.Pose d)
    (z : Contact.Cell d) : ProductClosure.World.poseCellIndex (toRegistered p) z = p.cell z := by
  funext i
  cases h : p.negative i <;>
    simp [ProductClosure.World.poseCellIndex, toRegistered, Contact.Pose.cell,
      Contact.Pose.sign, h] <;> ring

/-- The realized Euclidean map uses the affine anchor, with no spurious
negative-row correction on points. -/
@[simp] theorem poseIsometry_apply {m : ℕ} (p : Contact.Pose (m+1))
    (x : PhysicalRegistration.NativeChair.Space m) (i : Fin (m+1)) :
    PhysicalRegistration.NativeChair.poseIsometry (toRegistered p) x i =
      (p.sign i : ℝ) * x (p.perm i) + (p.shift i : ℝ) := by
  exact PhysicalRegistration.NativeChair.poseIsometry_apply (toRegistered p) x i

/-- Exact agreement of the original scaled-vertex action with the actual
Euclidean realization, for every nonzero denominator. -/
theorem scaledPoint_realizes {m : ℕ} (p : Contact.Pose (m+1)) (den : ℤ)
    (hden : den ≠ 0) (x : Contact.ScaledPoint (m+1)) (i : Fin (m+1)) :
    PhysicalRegistration.NativeChair.poseIsometry (toRegistered p)
      (WithLp.toLp 2 (fun j => (x j : ℝ) / (den : ℝ))) i =
        (p.scaledPoint den x i : ℝ) / (den : ℝ) := by
  rw [poseIsometry_apply]
  change (p.sign i : ℝ) * ((x (p.perm i) : ℝ) / (den : ℝ)) + (p.shift i : ℝ) = _
  simp only [Contact.Pose.scaledPoint, Int.cast_add, Int.cast_mul]
  have hd : (den : ℝ) ≠ 0 := by exact_mod_cast hden
  field_simp

/-- The cell footprint is transported exactly, for any finite carrier. -/
theorem placedCells_eq {d : ℕ} (S : Finset (Contact.Cell d)) (p : Contact.Pose d) :
    ProductClosure.World.placedCells S (toRegistered p) = p.cell '' (S : Set _) := by
  unfold ProductClosure.World.placedCells
  congr 1
  funext z
  exact poseCellIndex_toRegistered p z

/-- Full-state translations preserve all signed-frame data under the adapter.
The old translation formula is written explicitly here so the basic adapter
need not depend on the long recovered hierarchy-period replay. -/
theorem translate_toRegistered_formula {d : ℕ} (v : Contact.Cell d)
    (p : Contact.Pose d) :
    toRegistered { p with shift := fun i => p.shift i + v i } =
      RegisteredPrime.AtlasPeriods.translate v (toRegistered p) := by
  apply RegisteredPrime.Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  exact add_comm (p.shift i) (v i)

#print axioms poseEquiv
#print axioms poseCellIndex_toRegistered
#print axioms scaledPoint_realizes
#print axioms placedCells_eq
end
end ClarkSeed.PoseAdapter
