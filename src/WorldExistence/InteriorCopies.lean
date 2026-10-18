module
public import WorldExistence.FiniteStages
@[expose] public section
namespace RegisteredPrime.WorldExistence

/-- Empty outer, then central: an actual interior depth-two copy. -/
noncomputable def interiorCopy (P : Parameters) : Pose P.p :=
  refine P (arithmeticChild P (.outer (fun _ => false) (empty_proper P))) .central

theorem interiorCopy_descendant (P : Parameters) :
    Descendant P 2 (identityPose P.p) (interiorCopy P) := by
  apply (descendant_succ_iff P 1 (identityPose P.p) _).mpr
  exact ⟨arithmeticChild P (.outer (fun _ => false) (empty_proper P)), .central,
    child_is_descendant P _, Pose.Same.refl _⟩

theorem interiorCopy_negative (P : Parameters) (i : Fin P.p) :
    (interiorCopy P).frame.negative i = false := by
  rw [interiorCopy, refine_central_negative, child_outer_negative]

theorem interiorCopy_anchor (P : Parameters) (i : Fin P.p) :
    (interiorCopy P).anchor i = 1 := by
  rw [interiorCopy, refine_central_anchor, child_outer_anchor]
  simp [RegisteredFrame.sign, child_outer_negative]

/-- The cumulative translation used to place the increasing finite patches. -/
def inset : Nat → Int
  | 0 => 0
  | k + 1 => inset k + sideLength (2 * k)

noncomputable def stageOrigin (P : Parameters) : Nat → Pose P.p
  | 0 => identityPose P.p
  | k + 1 => (stageOrigin P k).comp (scalePose (2 * k) (interiorCopy P)).inv

theorem positive_inv_anchor {p : Nat} (q : Pose p) (d : Int)
    (hn : ∀ i, q.frame.negative i = false) (ha : ∀ i, q.anchor i = d) :
    ∀ i, q.inv.anchor i = -d := by
  intro i
  simp [Pose.inv, RegisteredFrame.linear, RegisteredFrame.sign, RegisteredFrame.inv, hn, ha]

/-- No scalar-period assumption is needed: positive permutations fix every
constant coordinate vector, hence the anchors follow a scalar recurrence. -/
theorem stageOrigin_geometry (P : Parameters) (k : Nat) :
    (∀ i, (stageOrigin P k).frame.negative i = false) ∧
      (∀ i, (stageOrigin P k).anchor i = -(inset k)) := by
  induction k with
  | zero => simp [stageOrigin, identityPose, inset]
  | succ k ih =>
    have hn : ∀ i, (scalePose (2 * k) (interiorCopy P)).frame.negative i = false := by
      intro i
      rw [scalePose_frame]
      exact interiorCopy_negative P i
    have ha : ∀ i, (scalePose (2 * k) (interiorCopy P)).anchor i = sideLength (2 * k) := by
      intro i
      rw [scalePose_anchor, interiorCopy_anchor]
      simp
    have hai := positive_inv_anchor _ _ hn ha
    constructor
    · intro i
      change xor ((stageOrigin P k).frame.negative i)
        ((scalePose (2 * k) (interiorCopy P)).inv.frame.negative
          ((stageOrigin P k).frame.perm i)) = false
      rw [ih.1 i]
      change xor false ((scalePose (2 * k) (interiorCopy P)).frame.negative _) = false
      rw [hn]
      rfl
    · intro i
      change (stageOrigin P k).anchor i + (stageOrigin P k).frame.sign i *
        (scalePose (2 * k) (interiorCopy P)).inv.anchor ((stageOrigin P k).frame.perm i) =
          -(inset k + sideLength (2 * k))
      rw [ih.2 i, hai]
      simp only [RegisteredFrame.sign, ih.1 i, Bool.false_eq_true, ite_false, Int.one_mul]
      omega

theorem sideLength_two_step (k : Nat) : sideLength (2 * (k + 1)) = 4 * sideLength (2 * k) := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
  simp only [sideLength]
  omega

/-- Both sides of the inscribed cubes tend to infinity, with explicit
integer margins that do not appeal to a limit or compactness theorem. -/
theorem stage_margins (k : Nat) :
    (k : Int) ≤ inset k ∧ (k : Int) + 1 ≤ sideLength (2 * k) - inset k := by
  induction k with
  | zero => simp [inset, sideLength]
  | succ k ih =>
    have hp := sideLength_pos (2 * k)
    rw [inset, sideLength_two_step]
    simp only [Int.natCast_add, Int.natCast_one]
    constructor <;> omega

/-- The literal finite-stage marked tile collection. -/
def AtStage (P : Parameters) (k : Nat) (q : Pose P.p) : Prop :=
  ∃ d, Descendant P (2 * k) (identityPose P.p) d ∧ q = (stageOrigin P k).comp d

/-- A stage embeds as the actual depth-two interior subsupertile of the next. -/
theorem stage_inclusion (P : Parameters) (k : Nat) (q : Pose P.p)
    (hq : AtStage P k q) : AtStage P (k + 1) q := by
  obtain ⟨d, hd, hq⟩ := hq
  let S := scalePose (2 * k) (interiorCopy P)
  have hsub : Descendant P (2 * k) (interiorCopy P) (S.comp d) := by
    have h := descendant_comp P (2 * k) (interiorCopy P) (identityPose P.p) d hd
    simpa only [Pose.comp_identity] using h
  have hnext : Descendant P (2 * (k + 1)) (identityPose P.p) (S.comp d) := by
    have h := descendant_concat P 2 (2 * k) (identityPose P.p) (interiorCopy P)
      (S.comp d) (interiorCopy_descendant P) hsub
    simpa only [show 2 + 2 * k = 2 * (k + 1) by omega] using h
  refine ⟨S.comp d, hnext, ?_⟩
  rw [hq]
  change (stageOrigin P k).comp d = ((stageOrigin P k).comp S.inv).comp (S.comp d)
  rw [Pose.comp_assoc, ← Pose.comp_assoc S.inv, Pose.inv_comp, Pose.identity_comp]

theorem stage_inclusion_add (P : Parameters) (k m : Nat) (q : Pose P.p)
    (hq : AtStage P k q) : AtStage P (k + m) q := by
  induction m with
  | zero => simpa using hq
  | succ m ih => exact stage_inclusion P (k + m) q ih

theorem stage_mono (P : Parameters) (k l : Nat) (hkl : k ≤ l) (q : Pose P.p)
    (hq : AtStage P k q) : AtStage P l q := by
  have he : l = k + (l - k) := by omega
  rw [he]
  exact stage_inclusion_add P k (l - k) q hq

/-- Explicit inverse coordinates for the translated positive stage frame. -/
theorem stageOrigin_inverse_cell (P : Parameters) (k : Nat) (c : Cell P.p) (i : Fin P.p) :
    (stageOrigin P k).inv.cell c i = c ((stageOrigin P k).frame.inverse i) + inset k := by
  have h := inverse_at (stageOrigin P k) c ((stageOrigin P k).frame.inverse i)
  rw [(stageOrigin P k).frame.right_inverse, (stageOrigin_geometry P k).1] at h
  simp only [Bool.false_eq_true, ite_false] at h
  rw [(stageOrigin_geometry P k).2] at h
  omega

/-- Every integer cell is covered at an explicitly bounded finite stage. -/
theorem stages_cover (P : Parameters) (c : Cell P.p) :
    ∃ k q, AtStage P k q ∧ Occupies q c := by
  obtain ⟨k, hk⟩ := cell_has_bound c
  have hm := stage_margins k
  have hcube : ∀ i, 0 ≤ (stageOrigin P k).inv.cell c i ∧
      (stageOrigin P k).inv.cell c i < sideLength (2 * k) := by
    intro i
    rw [stageOrigin_inverse_cell]
    have hi := hk ((stageOrigin P k).frame.inverse i)
    omega
  obtain ⟨d, hd, hdc⟩ := low_cube_cover P (2 * k) ((stageOrigin P k).inv.cell c) hcube
  refine ⟨k, (stageOrigin P k).comp d, ⟨d, hd, rfl⟩, ?_⟩
  exact (occupies_comp_iff _ _ _).mpr hdc

end RegisteredPrime.WorldExistence
