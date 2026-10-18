module

public import SparseMonotiles.CoarseContactCertificatesFields
public import SparseMonotiles.CarrierHierarchyForwardCompleteness
public import SparseMonotiles.CarrierHierarchyRefinement

@[expose] public section

/-! Fast exact field checks for forward substitution pairs. Rejection checks
certify actual noncontact by coordinate gaps, and refine the trusted complete
NoContactCertificate interface. Member checks prove exact pose equality. -/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def CoarseFields.compose (p q : CoarseFields) : CoarseFields :=
  ⟨fun i => q.axis (p.axis i), fun i => xor (p.negative i) (q.negative (p.axis i)),
   fun i => p.sign i * q.shift (p.axis i) + p.shift i⟩

def CoarseFields.dilate (p : CoarseFields) : CoarseFields :=
  ⟨p.axis, p.negative, fun i => 2 * p.shift i⟩

theorem CoarseFields.compose_represents {d : ℕ} {pc qc : CoarseFields} {p q : Pose d}
    (hp : pc.Represents p) (hq : qc.Represents q) :
    (pc.compose qc).Represents (CarrierHierarchy.compose p q) := by
  intro i
  have hi := hp i
  have hj := hq (p.perm i)
  change qc.axis (pc.axis i.val) = _ ∧
    xor (pc.negative i.val) (qc.negative (pc.axis i.val)) = _ ∧
    pc.sign i.val * qc.shift (pc.axis i.val) + pc.shift i.val = _
  simp only [CoarseFields.sign, hi.1, hi.2.1, hi.2.2, hj.1, hj.2.1, hj.2.2]
  exact ⟨rfl, rfl, rfl⟩

theorem CoarseFields.dilate_represents {d : ℕ} {pc : CoarseFields} {p : Pose d}
    (hp : pc.Represents p) : pc.dilate.Represents (dilatePose p) := by
  intro i
  exact ⟨(hp i).1, (hp i).2.1, congrArg (2 * ·) (hp i).2.2⟩

def CoarseFields.lower (p : CoarseFields) (i : ℕ) : ℤ :=
  p.shift i - if p.negative i then 2 else 0

theorem CoarseFields.lower_eq {d : ℕ} {pc : CoarseFields} {p : Pose d}
    (hp : pc.Represents p) (i : Fin d) : pc.lower i.val = boxLower p i := by
  simp only [CoarseFields.lower, (hp i).2.1, (hp i).2.2, boxLower]

def forwardFieldsMatch (d : ℕ) (p q : CoarseFields) : Bool :=
  (List.range d).all fun i => decide (p.axis i = q.axis i) &&
    decide (p.negative i = q.negative i) && decide (p.shift i = q.shift i)

theorem forwardFieldsMatch_sound {d : ℕ} {pc qc : CoarseFields} {p q : Pose d}
    (hp : pc.Represents p) (hq : qc.Represents q)
    (h : forwardFieldsMatch d pc qc = true) : p = q := by
  apply coarsePoseMatchB_sound
  apply List.all_eq_true.mpr
  intro i _
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simp only [(hp i).1, (hp i).2.1, (hp i).2.2, (hq i).1, (hq i).2.1, (hq i).2.2,
    Bool.and_eq_true, decide_eq_true_eq] at hi
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨Fin.ext hi.1.1, hi.1.2⟩, hi.2⟩

def ForwardGap (p q : ℤ) (margin : ℤ) : Prop := p + margin < q ∨ q + margin < p
instance (p q margin : ℤ) : Decidable (ForwardGap p q margin) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem forward_far_noncontact {d : ℕ} {p q : Pose d} (j : Fin d)
    (h : ForwardGap (boxLower p j) (boxLower q j) 2) : ¬ CellContact p q := by
  rintro ⟨c, e, hc, he, k, hk, ho⟩
  have hp := (occupies_box_iff p c).mp hc |>.1 j
  have hq := (occupies_box_iff q e).mp he |>.1 j
  unfold ForwardGap at h
  by_cases hj : j = k
  · subst k
    omega
  · have hh := ho j hj
    omega

theorem forward_two_gap_noncontact {d : ℕ} {p q : Pose d} (j k : Fin d) (hne : j ≠ k)
    (hj : ForwardGap (boxLower p j) (boxLower q j) 1)
    (hk : ForwardGap (boxLower p k) (boxLower q k) 1) : ¬ CellContact p q := by
  rintro ⟨c, e, hc, he, axis, ha, ho⟩
  have hgap : ∀ i, ForwardGap (boxLower p i) (boxLower q i) 1 → i = axis := by
    intro i hi
    by_contra hia
    have hp := (occupies_box_iff p c).mp hc |>.1 i
    have hq := (occupies_box_iff q e).mp he |>.1 i
    have hh := ho i hia
    unfold ForwardGap at hi
    omega
  exact hne ((hgap j hj).trans (hgap k hk).symm)

inductive ForwardFieldsWitness (d : ℕ) (κ : Type) where
  | member (index : κ)
  | gap (left right : Fin d)

def ForwardFieldsWitness.check {d : ℕ} {κ : Type} (registry : κ → CoarseFields)
    (p q : CoarseFields) : ForwardFieldsWitness d κ → Bool
  | .member i => forwardFieldsMatch d (p.compose (registry i)) q
  | .gap j k => if j = k then decide (ForwardGap (p.lower j.val) (q.lower j.val) 2)
    else decide (ForwardGap (p.lower j.val) (q.lower j.val) 1) &&
      decide (ForwardGap (p.lower k.val) (q.lower k.val) 1)

def ForwardFieldsWitness.toWitness {d : ℕ} {κ : Type} :
    ForwardFieldsWitness d κ → ForwardPairWitness κ
  | .member i => .member i
  | .gap _ _ => .apart

theorem ForwardFieldsWitness.check_sound {d : ℕ} {κ : Type}
    (registry : κ → Pose d) (fields : κ → CoarseFields)
    (hr : ∀ i, (fields i).Represents (registry i))
    {pc qc : CoarseFields} {p q : Pose d} (hp : pc.Represents p) (hq : qc.Represents q)
    {w : ForwardFieldsWitness d κ} (h : w.check fields pc qc = true) :
    w.toWitness.Valid registry p q := by
  cases w with
  | member i =>
    have he := forwardFieldsMatch_sound (CoarseFields.compose_represents hp (hr i)) hq h
    change normalize p q = registry i
    rw [← he]
    simp only [normalize, ← compose_assoc, inversePose_compose, compose_root_left]
  | gap j k =>
    change NoContactCertificate p q
    apply noContactCertificate_complete
    by_cases hjk : j = k
    · have hh : ForwardGap (pc.lower j.val) (qc.lower j.val) 2 := by
        simpa only [ForwardFieldsWitness.check, if_pos hjk, decide_eq_true_eq] using h
      rw [CoarseFields.lower_eq hp j, CoarseFields.lower_eq hq j] at hh
      exact forward_far_noncontact j hh
    · have hh : ForwardGap (pc.lower j.val) (qc.lower j.val) 1 ∧
          ForwardGap (pc.lower k.val) (qc.lower k.val) 1 := by
        simpa only [ForwardFieldsWitness.check, if_neg hjk, Bool.and_eq_true, decide_eq_true_eq] using h
      rw [CoarseFields.lower_eq hp j, CoarseFields.lower_eq hq j, CoarseFields.lower_eq hp k, CoarseFields.lower_eq hq k] at hh
      exact forward_two_gap_noncontact j k hjk hh.1 hh.2

#print axioms ForwardFieldsWitness.check_sound
end SparseMonotiles.CarrierHierarchy
