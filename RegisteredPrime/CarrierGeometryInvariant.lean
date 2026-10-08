module
public import RegisteredPrime.WorldRecognitionBridge
@[expose] public section
namespace RegisteredPrime
def CarrierEquivalent {p : Nat} (q r : Pose p) : Prop :=
  (∀ i, q.frame.negative i = r.frame.negative i) ∧ ∀ i, q.anchor i = r.anchor i
theorem CarrierEquivalent.refl {p : Nat} (q : Pose p) : CarrierEquivalent q q :=
  ⟨fun _ => rfl, fun _ => rfl⟩
theorem CarrierEquivalent.symm {p : Nat} {q r : Pose p} (h : CarrierEquivalent q r) :
    CarrierEquivalent r q := ⟨fun i => (h.1 i).symm, fun i => (h.2 i).symm⟩
theorem CarrierEquivalent.trans {p : Nat} {q r s : Pose p}
    (h : CarrierEquivalent q r) (k : CarrierEquivalent r s) : CarrierEquivalent q s :=
  ⟨fun i => (h.1 i).trans (k.1 i), fun i => (h.2 i).trans (k.2 i)⟩
theorem Pose.Same.carrier {p : Nat} {q r : Pose p} (h : q.Same r) : CarrierEquivalent q r := h.2
theorem CarrierEquivalent.occupies_iff {p : Nat} {q r : Pose p}
    (h : CarrierEquivalent q r) (c : Cell p) : Occupies q c ↔ Occupies r c := by
  have hb : boxLower q = boxLower r := by
    funext i
    simp only [boxLower]
    rw [h.1 i, h.2 i]
  have hh : hole q = hole r := by
    funext i
    rw [hole_coordinate, hole_coordinate, h.1 i, h.2 i]
  rw [occupies_box_iff, occupies_box_iff, hb, hh]
structure CarrierRule (p : Nat) where
  child : Role p → Pose p
  central_negative : ∀ i, (child .central).frame.negative i = false
  central_anchor : ∀ i, (child .central).anchor i = 1
  outer_negative : ∀ A hA i, (child (.outer A hA)).frame.negative i = A i
  outer_anchor : ∀ A hA i, (child (.outer A hA)).anchor i = if A i then 4 else 0
noncomputable def arithmeticCarrierRule (P : Parameters) : CarrierRule P.p where
  child := arithmeticChild P
  central_negative := fun _ => rfl
  central_anchor := fun _ => rfl
  outer_negative := fun A _ i => outerFrame_neg P A i
  outer_anchor := fun _ _ _ => rfl
def refineWith {p : Nat} (R : CarrierRule p) (q : Pose p) (a : Role p) : Pose p :=
  ({ frame := q.frame, anchor := fun i => 2 * q.anchor i } : Pose p).comp (R.child a)
@[simp] theorem arithmetic_refineWith (P : Parameters) (q : Pose P.p) (a : Role P.p) :
    refineWith (arithmeticCarrierRule P) q a = refine P q a := rfl
def reindexRole {p : Nat} (q r : Pose p) (A : Mask p) : Mask p :=
  fun j => A (q.frame.perm (r.frame.inverse j))
@[simp] theorem reindexRole_at {p : Nat} (q r : Pose p) (A : Mask p) (i : Fin p) :
    reindexRole q r A (r.frame.perm i) = A (q.frame.perm i) := by
  simp [reindexRole, r.frame.left_inverse]
theorem reindexRole_proper {p : Nat} (q r : Pose p) (A : Mask p) (hA : Proper A) :
    Proper (reindexRole q r A) := by
  obtain ⟨j, hj⟩ := hA
  refine ⟨r.frame.perm (q.frame.inverse j), ?_⟩
  rw [reindexRole_at, q.frame.right_inverse]
  exact hj
theorem refinement_carrier_correspondence {p : Nat} (R S : CarrierRule p)
    (q r : Pose p) (hqr : CarrierEquivalent q r) (a : Role p) :
    ∃ b : Role p, CarrierEquivalent (refineWith R q a) (refineWith S r b) := by
  cases a with
  | central =>
    refine ⟨.central, ?_, ?_⟩
    · intro i
      change xor (q.frame.negative i) ((R.child .central).frame.negative (q.frame.perm i)) =
        xor (r.frame.negative i) ((S.child .central).frame.negative (r.frame.perm i))
      rw [R.central_negative, S.central_negative, hqr.1 i]
    · intro i
      change 2 * q.anchor i + q.frame.sign i * (R.child .central).anchor (q.frame.perm i) =
        2 * r.anchor i + r.frame.sign i * (S.child .central).anchor (r.frame.perm i)
      rw [R.central_anchor, S.central_anchor, hqr.2 i]
      simp only [RegisteredFrame.sign, hqr.1 i]
  | outer A hA =>
    let B := reindexRole q r A
    have hB : Proper B := reindexRole_proper q r A hA
    refine ⟨.outer B hB, ?_, ?_⟩
    · intro i
      change xor (q.frame.negative i) ((R.child (.outer A hA)).frame.negative (q.frame.perm i)) =
        xor (r.frame.negative i) ((S.child (.outer B hB)).frame.negative (r.frame.perm i))
      rw [R.outer_negative, S.outer_negative, hqr.1 i]
      exact congrArg (fun b => xor (r.frame.negative i) b) (reindexRole_at q r A i).symm
    · intro i
      change 2 * q.anchor i + q.frame.sign i * (R.child (.outer A hA)).anchor (q.frame.perm i) =
        2 * r.anchor i + r.frame.sign i * (S.child (.outer B hB)).anchor (r.frame.perm i)
      rw [R.outer_anchor, S.outer_anchor, hqr.2 i]
      simp only [B, reindexRole_at, RegisteredFrame.sign, hqr.1 i]
def RuleDescendant {p : Nat} (R : CarrierRule p) : Nat → Pose p → Pose p → Prop
  | 0, q, t => q.Same t
  | n + 1, q, t => ∃ a, RuleDescendant R n (refineWith R q a) t
theorem descendant_carrier_correspondence {p : Nat} (R S : CarrierRule p)
    (n : Nat) (q r : Pose p) (hqr : CarrierEquivalent q r) (t : Pose p)
    (ht : RuleDescendant R n q t) :
    ∃ u, RuleDescendant S n r u ∧ CarrierEquivalent t u := by
  induction n generalizing q r with
  | zero =>
    exact ⟨r, ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩, ht.carrier.symm.trans hqr⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ht
    obtain ⟨b, hb⟩ := refinement_carrier_correspondence R S q r hqr a
    obtain ⟨u, hu, htu⟩ := ih _ _ hb ha
    exact ⟨u, ⟨b, hu⟩, htu⟩
theorem arithmetic_descendant_iff (P : Parameters) (n : Nat) (q t : Pose P.p) :
    RuleDescendant (arithmeticCarrierRule P) n q t ↔ Descendant P n q t := by
  induction n generalizing q with
  | zero => exact Iff.rfl
  | succ n ih =>
    change (∃ a, RuleDescendant (arithmeticCarrierRule P) n
      (refineWith (arithmeticCarrierRule P) q a) t) ↔
      ∃ a, Descendant P n (refine P q a) t
    simp only [arithmetic_refineWith, ih]
def canonicalCarrierRule (p : Nat) : CarrierRule p where
  child := fun a => match a with
    | .central => {
      frame := (identityPose p).frame
      anchor := fun _ => 1
    }
    | .outer A _ => {
      frame := { (identityPose p).frame with negative := A }
      anchor := fun i => if A i then 4 else 0
    }
  central_negative := fun _ => rfl
  central_anchor := fun _ => rfl
  outer_negative := fun _ _ _ => rfl
  outer_anchor := fun _ _ _ => rfl
theorem arithmetic_to_canonical_carriers (P : Parameters) (n : Nat) (t : Pose P.p)
    (ht : Descendant P n (identityPose P.p) t) :
    ∃ u, RuleDescendant (canonicalCarrierRule P.p) n (identityPose P.p) u ∧
      CarrierEquivalent t u :=
  descendant_carrier_correspondence (arithmeticCarrierRule P) (canonicalCarrierRule P.p)
    n _ _ (CarrierEquivalent.refl _) t ((arithmetic_descendant_iff P n _ _).mpr ht)
end RegisteredPrime
