module
public import RegisteredPrime.CarrierGeometryInvariant
@[expose] public section
namespace RegisteredPrime
def OuterColored {p : Nat} (q : Pose p) : Prop :=
  (∀ i, boxLower q i % 2 = 0) ∧
  ∃ b : Bool, ∀ i, (boxLower q i / 2 - bit (q.frame.negative i)) % 2 = bit b
def CentralColored {p : Nat} (q : Pose p) : Prop :=
  (∀ i, boxLower q i % 2 = 1) ∧
  ∃ b : Bool, ∀ i, (boxLower q i / 2) % 2 = bit b
def CarrierColored {p : Nat} (q : Pose p) : Prop := OuterColored q ∨ CentralColored q
@[simp] theorem refine_outer_negative (P : Parameters) (q : Pose P.p)
    (A : Mask P.p) (hA : Proper A) (i : Fin P.p) :
    (refine P q (.outer A hA)).frame.negative i =
      xor (q.frame.negative i) (A (q.frame.perm i)) := by
  change xor (q.frame.negative i) ((outerFrame P A).neg (q.frame.perm i).val) = _
  rw [outerFrame_neg]
@[simp] theorem refine_outer_anchor (P : Parameters) (q : Pose P.p)
    (A : Mask P.p) (hA : Proper A) (i : Fin P.p) :
    (refine P q (.outer A hA)).anchor i =
      2 * q.anchor i + q.frame.sign i * (if A (q.frame.perm i) then 4 else 0) := rfl
@[simp] theorem refine_central_negative (P : Parameters) (q : Pose P.p) (i : Fin P.p) :
    (refine P q .central).frame.negative i = q.frame.negative i := by
  change xor (q.frame.negative i) false = q.frame.negative i
  simp
@[simp] theorem refine_central_anchor (P : Parameters) (q : Pose P.p) (i : Fin P.p) :
    (refine P q .central).anchor i = 2 * q.anchor i + q.frame.sign i := by
  change 2 * q.anchor i + q.frame.sign i * 1 = _
  simp
theorem refine_outer_lower (P : Parameters) (q : Pose P.p) (A : Mask P.p)
    (hA : Proper A) (i : Fin P.p) :
    boxLower (refine P q (.outer A hA)) i =
      2 * boxLower q i + 2 * bit ((refine P q (.outer A hA)).frame.negative i) := by
  simp only [boxLower, refine_outer_anchor, refine_outer_negative, RegisteredFrame.sign, bit]
  by_cases hn : q.frame.negative i = true <;>
    by_cases ha : A (q.frame.perm i) = true <;> simp [hn, ha] <;> omega
theorem refine_central_lower (P : Parameters) (q : Pose P.p) (i : Fin P.p) :
    boxLower (refine P q .central) i = 2 * boxLower q i + 1 := by
  simp only [boxLower, refine_central_anchor, refine_central_negative, RegisteredFrame.sign, bit]
  by_cases hn : q.frame.negative i = true <;> simp [hn] <;> omega
theorem refine_carrier_colored (P : Parameters) (q : Pose P.p) (hq : q.UniformParity)
    (a : Role P.p) : CarrierColored (refine P q a) := by
  obtain ⟨b, hb⟩ := hq
  have hbox := uniform_parity_box q b hb
  cases a with
  | central =>
    right
    constructor
    · intro i
      rw [refine_central_lower]
      omega
    · refine ⟨b, fun i => ?_⟩
      rw [refine_central_lower]
      have he : (2 * boxLower q i + 1) / 2 = boxLower q i := by omega
      rw [he]
      exact hbox i
  | outer A hA =>
    left
    constructor
    · intro i
      rw [refine_outer_lower]
      omega
    · refine ⟨b, fun i => ?_⟩
      rw [refine_outer_lower]
      have he : (2 * boxLower q i +
          2 * bit ((refine P q (.outer A hA)).frame.negative i)) / 2 -
          bit ((refine P q (.outer A hA)).frame.negative i) = boxLower q i := by omega
      rw [he]
      exact hbox i
theorem Pose.Same.carrier_colored {p : Nat} {q r : Pose p} (h : q.Same r)
    (hq : CarrierColored q) : CarrierColored r := by
  have hb := h.boxLower
  rcases hq with ⟨he, b, hb'⟩ | ⟨ho, b, hb'⟩
  · left
    refine ⟨fun i => by rw [← hb]; exact he i, b, fun i => ?_⟩
    rw [← hb, ← h.2.1 i]
    exact hb' i
  · right
    exact ⟨fun i => by rw [← hb]; exact ho i, b, fun i => by rw [← hb]; exact hb' i⟩
theorem descendant_carrier_colored (P : Parameters) (n : Nat) (q t : Pose P.p)
    (hqu : q.UniformParity) (hqc : CarrierColored q) (ht : Descendant P n q t) :
    CarrierColored t := by
  induction n generalizing q with
  | zero => exact Pose.Same.carrier_colored ht hqc
  | succ n ih =>
    obtain ⟨a, ha⟩ := ht
    exact ih _ (refine_uniform_parity P q a) (refine_carrier_colored P q hqu a) ha
theorem generated_tile_carrier_colored (P : Parameters) (n : Nat) (q : Pose P.p)
    (hq : Descendant P n (identityPose P.p) q) : CarrierColored q := by
  have hu : (identityPose P.p).UniformParity := ⟨false, fun _ => rfl⟩
  have hc : CarrierColored (identityPose P.p) := Or.inl ⟨fun _ => rfl, false, fun _ => rfl⟩
  exact descendant_carrier_colored P n _ q hu hc hq
end RegisteredPrime
