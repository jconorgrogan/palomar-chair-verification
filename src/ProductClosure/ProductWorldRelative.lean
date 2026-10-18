module

public import ProductClosure.ProductWorldSplit

@[expose] public section

/-! Exact compatibility of factor-pose splitting with relative contacts.
This turns a relative product mate language into the binary full-state
neighbor law used by Cartesian decoding. -/
namespace ProductClosure.World

noncomputable section
variable {m n : ℕ}

theorem preservesBlocks_identity : PreservesBlocks (RegisteredPrime.identityPose (m + n)) :=
  fun _ => Iff.rfl

theorem PreservesBlocks.comp {q r : RegisteredPrime.Pose (m + n)}
    (hq : PreservesBlocks q) (hr : PreservesBlocks r) : PreservesBlocks (q.comp r) :=
  fun i => (hr (q.frame.perm i)).trans (hq i)

theorem PreservesBlocks.inv {q : RegisteredPrime.Pose (m + n)}
    (hq : PreservesBlocks q) : PreservesBlocks q.inv := inverse_preservesBlocks q hq

theorem PreservesBlocks.relative {q r : RegisteredPrime.Pose (m + n)}
    (hq : PreservesBlocks q) (hr : PreservesBlocks r) : PreservesBlocks (q.relative r) :=
  hq.inv.comp hr

@[simp] theorem leftPose_identity :
    leftPose (RegisteredPrime.identityPose (m + n)) preservesBlocks_identity =
      RegisteredPrime.identityPose m := by
  apply RegisteredPrime.Pose.Same.eq
  constructor
  · intro i; apply Fin.ext; rfl
  constructor <;> intro i <;> rfl

@[simp] theorem rightPose_identity :
    rightPose (RegisteredPrime.identityPose (m + n)) preservesBlocks_identity =
      RegisteredPrime.identityPose n := by
  apply RegisteredPrime.Pose.Same.eq
  constructor
  · intro i; apply Fin.ext
    change m + i.val - m = i.val
    omega
  constructor <;> intro i <;> rfl

theorem leftPose_comp (q r : RegisteredPrime.Pose (m + n))
    (hq : PreservesBlocks q) (hr : PreservesBlocks r) :
    leftPose (q.comp r) (hq.comp hr) = (leftPose q hq).comp (leftPose r hr) := by
  apply RegisteredPrime.Pose.Same.eq
  constructor
  · intro i
    apply Fin.ext
    have he : Fin.castAdd n (leftPerm (q.comp r) (hq.comp hr) i) =
        Fin.castAdd n (leftPerm r hr (leftPerm q hq i)) := by
      rw [castAdd_leftPerm, castAdd_leftPerm, castAdd_leftPerm]
      rfl
    have hv := congrArg Fin.val he
    exact hv
  constructor
  · intro i
    change xor (q.frame.negative (Fin.castAdd n i))
      (r.frame.negative (q.frame.perm (Fin.castAdd n i))) =
      xor (q.frame.negative (Fin.castAdd n i))
      (r.frame.negative (Fin.castAdd n (leftPerm q hq i)))
    rw [castAdd_leftPerm]
  · intro i
    change q.anchor (Fin.castAdd n i) + q.frame.sign (Fin.castAdd n i) *
      r.anchor (q.frame.perm (Fin.castAdd n i)) =
      q.anchor (Fin.castAdd n i) + (leftPose q hq).frame.sign i *
      r.anchor (Fin.castAdd n (leftPerm q hq i))
    rw [castAdd_leftPerm]
    rfl

theorem rightPose_comp (q r : RegisteredPrime.Pose (m + n))
    (hq : PreservesBlocks q) (hr : PreservesBlocks r) :
    rightPose (q.comp r) (hq.comp hr) = (rightPose q hq).comp (rightPose r hr) := by
  apply RegisteredPrime.Pose.Same.eq
  constructor
  · intro i
    apply Fin.ext
    have he : Fin.natAdd m (rightPerm (q.comp r) (hq.comp hr) i) =
        Fin.natAdd m (rightPerm r hr (rightPerm q hq i)) := by
      rw [natAdd_rightPerm, natAdd_rightPerm, natAdd_rightPerm]
      rfl
    have hv := congrArg Fin.val he
    simp only [Fin.val_natAdd] at hv
    change (rightPerm (q.comp r) (hq.comp hr) i).val =
      (rightPerm r hr (rightPerm q hq i)).val
    exact Nat.add_left_cancel hv
  constructor
  · intro i
    change xor (q.frame.negative (Fin.natAdd m i))
      (r.frame.negative (q.frame.perm (Fin.natAdd m i))) =
      xor (q.frame.negative (Fin.natAdd m i))
      (r.frame.negative (Fin.natAdd m (rightPerm q hq i)))
    rw [natAdd_rightPerm]
  · intro i
    change q.anchor (Fin.natAdd m i) + q.frame.sign (Fin.natAdd m i) *
      r.anchor (q.frame.perm (Fin.natAdd m i)) =
      q.anchor (Fin.natAdd m i) + (rightPose q hq).frame.sign i *
      r.anchor (Fin.natAdd m (rightPerm q hq i))
    rw [natAdd_rightPerm]
    rfl

@[simp] theorem leftPose_inv (q : RegisteredPrime.Pose (m + n)) (hq : PreservesBlocks q) :
    leftPose q.inv hq.inv = (leftPose q hq).inv := by
  apply RegisteredPrime.Pose.inverse_unique
  have h := leftPose_comp q q.inv hq hq.inv
  simpa only [RegisteredPrime.Pose.comp_inv, leftPose_identity] using h.symm

@[simp] theorem rightPose_inv (q : RegisteredPrime.Pose (m + n)) (hq : PreservesBlocks q) :
    rightPose q.inv hq.inv = (rightPose q hq).inv := by
  apply RegisteredPrime.Pose.inverse_unique
  have h := rightPose_comp q q.inv hq hq.inv
  simpa only [RegisteredPrime.Pose.comp_inv, rightPose_identity] using h.symm

/-- Active restrictions commute with exact relative-pose computation. -/
theorem leftPose_relative (q r : RegisteredPrime.Pose (m + n))
    (hq : PreservesBlocks q) (hr : PreservesBlocks r) :
    leftPose (q.relative r) (hq.relative hr) = (leftPose q hq).relative (leftPose r hr) := by
  change leftPose (q.inv.comp r) (hq.inv.comp hr) = _
  rw [leftPose_comp q.inv r hq.inv hr, leftPose_inv q hq]
  rfl

/-- Passive restrictions commute with exact relative-pose computation. -/
theorem rightPose_relative (q r : RegisteredPrime.Pose (m + n))
    (hq : PreservesBlocks q) (hr : PreservesBlocks r) :
    rightPose (q.relative r) (hq.relative hr) = (rightPose q hq).relative (rightPose r hr) := by
  change rightPose (q.inv.comp r) (hq.inv.comp hr) = _
  rw [rightPose_comp q.inv r hq.inv hr, rightPose_inv q hq]
  rfl

theorem relative_identity_iff {d : ℕ} (q r : RegisteredPrime.Pose d) :
    q.relative r = RegisteredPrime.identityPose d ↔ q = r := by
  constructor
  · intro h
    have he := q.comp_relative r
    rw [h, RegisteredPrime.Pose.comp_identity] at he
    exact he
  · rintro rfl
    exact q.inv_comp

/-- The unary relative product language includes complete identity of the
passive factor pose, not merely its frame, occupied cell, or orientation. -/
def RelativeProductLanguage
    (MA : RegisteredPrime.Pose m → Prop) (MB : RegisteredPrime.Pose n → Prop)
    (e : RegisteredPrime.Pose (m + n)) : Prop :=
  ∃ he : PreservesBlocks e,
    (MA (leftPose e he) ∧ rightPose e he = RegisteredPrime.identityPose n) ∨
    (leftPose e he = RegisteredPrime.identityPose m ∧ MB (rightPose e he))

/-- Exact relative product contact closure supplies the full placed-state
neighbor language. This is the algebraic bridge used by world decoding. -/
theorem productLanguage_of_relative
    {MA : RegisteredPrime.Pose m → Prop} {MB : RegisteredPrime.Pose n → Prop}
    (q r : RegisteredPrime.Pose (m + n)) (hq : PreservesBlocks q) (hr : PreservesBlocks r)
    (hcontact : RelativeProductLanguage MA MB (q.relative r)) :
    ProductLanguage (fun a b => MA (a.relative b)) (fun a b => MB (a.relative b))
      (leftPose q hq, rightPose q hq) (leftPose r hr, rightPose r hr) := by
  obtain ⟨he, h | h⟩ := hcontact
  · have hA : MA ((leftPose q hq).relative (leftPose r hr)) := by
      rw [← leftPose_relative q r hq hr]
      exact h.1
    have hB : rightPose q hq = rightPose r hr := by
      apply (relative_identity_iff _ _).mp
      rw [← rightPose_relative q r hq hr]
      exact h.2
    exact Or.inl ⟨hA, hB⟩
  · have hA : leftPose q hq = leftPose r hr := by
      apply (relative_identity_iff _ _).mp
      rw [← leftPose_relative q r hq hr]
      exact h.1
    have hB : MB ((rightPose q hq).relative (rightPose r hr)) := by
      rw [← rightPose_relative q r hq hr]
      exact h.2
    exact Or.inr ⟨hA, hB⟩

#print axioms leftPose_relative
#print axioms rightPose_relative
#print axioms productLanguage_of_relative

end
end ProductClosure.World
