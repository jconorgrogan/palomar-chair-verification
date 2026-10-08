module
public import RegisteredPrime.UniqueParent
@[expose] public section
namespace RegisteredPrime

/-- Integer unit cells of an unscaled doubled parent. -/
def DoubledOccupies {p : Nat} (t : Pose p) (c : Cell p) : Prop :=
  DoubledChairCell (t.inv.cell c)

def DoubledDisjoint {p : Nat} (t u : Pose p) : Prop :=
  ∀ c, ¬ (DoubledOccupies t c ∧ DoubledOccupies u c)

def DoubledFaceContact {p : Nat} (t u : Pose p) : Prop :=
  DoubledDisjoint t u ∧ ∃ a b, DoubledOccupies t a ∧ DoubledOccupies u b ∧ Adjacent a b

/-- Every actual child contact across these two parents belongs to the language
of contacts generated inside finite arithmetic supertiles. -/
def ChildLegal (P : Parameters) (t u : Pose P.p) : Prop :=
  ∀ a b : Role P.p,
    FaceContact (t.comp (arithmeticChild P a)) (u.comp (arithmeticChild P b)) →
    GeneratedContact P ((t.comp (arithmeticChild P a)).relative
      (u.comp (arithmeticChild P b)))

theorem doubled_occupies_iff_child (P : Parameters) (t : Pose P.p) (c : Cell P.p) :
    DoubledOccupies t c ↔ ∃ a, Occupies (t.comp (arithmeticChild P a)) c := by
  change DoubledChairCell (t.inv.cell c) ↔ _
  rw [exact_child_cover P]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (occupies_comp_iff t (arithmeticChild P a) c).mpr ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (occupies_comp_iff t (arithmeticChild P a) c).mp ha⟩

theorem CompleteParent.doubled_disjoint (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (t u : Pose P.p) (ht : CompleteParent P W t)
    (hu : CompleteParent P W u) (hne : t ≠ u) : DoubledDisjoint t u := by
  intro c ⟨htc, huc⟩
  obtain ⟨a, ha⟩ := (doubled_occupies_iff_child P t c).mp htc
  obtain ⟨b, hb⟩ := (doubled_occupies_iff_child P u c).mp huc
  have he := (W.nonoverlap _ _ (ht a) (hu b) c ha hb).eq
  obtain ⟨v, _, _, hv⟩ := registered_unique_parent_pose P W hl _ (ht a)
  have htv := hv t ht ⟨a, rfl⟩
  have huv := hv u hu ⟨b, he⟩
  exact hne (htv.trans huv.symm)

theorem CompleteParent.child_legal (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (t u : Pose P.p) (ht : CompleteParent P W t)
    (hu : CompleteParent P W u) : ChildLegal P t u := by
  intro a b hc
  exact hl _ _ (ht a) (hu b) hc

/-- A face contact of doubled parents always has an actual child contact witness.
The quantifier ranges over the whole interface, without a level cutoff. -/
theorem doubled_contact_child_witness (P : Parameters) (t u : Pose P.p)
    (hc : DoubledFaceContact t u) :
    ∃ a b : Role P.p,
      FaceContact (t.comp (arithmeticChild P a)) (u.comp (arithmeticChild P b)) := by
  obtain ⟨hd, x, y, hx, hy, hxy⟩ := hc
  obtain ⟨a, ha⟩ := (doubled_occupies_iff_child P t x).mp hx
  obtain ⟨b, hb⟩ := (doubled_occupies_iff_child P u y).mp hy
  refine ⟨a, b, ?_, x, y, ha, hb, hxy⟩
  intro z ⟨haz, hbz⟩
  exact hd z ⟨(doubled_occupies_iff_child P t z).mpr ⟨a, haz⟩,
    (doubled_occupies_iff_child P u z).mpr ⟨b, hbz⟩⟩

/-- Recover a full parent-relative pose from a chosen pair of child roles and
an actual generated child-relative pose. This is a candidate formula, not a
claim that the recovered parent-relative pose itself belongs to E. -/
noncomputable def parentCandidate (P : Parameters) (a b : Role P.p) (k : Pose P.p) : Pose P.p :=
  ((arithmeticChild P a).comp k).comp (arithmeticChild P b).inv

theorem Pose.relative_child_factorization {p : Nat} (t u a b : Pose p) :
    (t.comp a).relative (u.comp b) = a.relative ((t.relative u).comp b) := by
  have he : u.comp b = t.comp ((t.relative u).comp b) := by
    rw [← Pose.comp_assoc, Pose.comp_relative]
  rw [he, Pose.relative_left_cancel]

theorem parent_candidate_reconstruction (P : Parameters) (t u : Pose P.p)
    (a b : Role P.p) :
    parentCandidate P a b ((t.comp (arithmeticChild P a)).relative
      (u.comp (arithmeticChild P b))) = t.relative u := by
  unfold parentCandidate
  rw [Pose.relative_child_factorization, Pose.comp_relative, Pose.comp_assoc,
    Pose.comp_inv, Pose.comp_identity]

/-- Exact exhaustive candidate reduction from all compatible generated child
contacts. No contact census, coarse closure, or hierarchy is assumed. -/
theorem child_legal_parent_candidate (P : Parameters) (t u : Pose P.p)
    (hc : DoubledFaceContact t u) (hl : ChildLegal P t u) :
    ∃ a b : Role P.p, ∃ k : Pose P.p,
      GeneratedContact P k ∧ t.relative u = parentCandidate P a b k := by
  obtain ⟨a, b, hab⟩ := doubled_contact_child_witness P t u hc
  exact ⟨a, b, _, hl a b hab, (parent_candidate_reconstruction P t u a b).symm⟩

theorem Pose.uniform_parity_comp {p : Nat} (q r : Pose p)
    (hq : q.UniformParity) (hr : r.UniformParity) : (q.comp r).UniformParity := by
  obtain ⟨b, hb⟩ := hq
  obtain ⟨c, hc⟩ := hr
  refine ⟨xor b c, fun i => ?_⟩
  have h1 := hb i
  have h2 := hc (q.frame.perm i)
  simp only [Pose.comp, RegisteredFrame.linear, RegisteredFrame.sign]
  cases b <;> cases c <;> by_cases hn : q.frame.negative i = true <;>
    simp [hn, bit] at h1 h2 ⊢ <;> omega

theorem Pose.uniform_parity_inv {p : Nat} (q : Pose p)
    (hq : q.UniformParity) : q.inv.UniformParity := by
  have h := q.uniform_parity_relative (identityPose p) hq ⟨false, fun _ => rfl⟩
  change (q.inv.comp (identityPose p)).UniformParity at h
  rwa [Pose.comp_identity] at h

theorem arithmeticChild_uniform_parity (P : Parameters) (a : Role P.p) :
    (arithmeticChild P a).UniformParity :=
  (identity_refine_same P a).uniform_parity (refine_uniform_parity P (identityPose P.p) a)

/-- Exact child legality forces every adjacent parent-relative translation to
have constant parity. Evenness is proved separately from geometric disjointness. -/
theorem child_legal_parent_constant_parity (P : Parameters) (t u : Pose P.p)
    (hc : DoubledFaceContact t u) (hl : ChildLegal P t u) :
    (t.relative u).UniformParity := by
  obtain ⟨a, b, k, hk, he⟩ := child_legal_parent_candidate P t u hc hl
  rw [he]
  exact Pose.uniform_parity_comp _ _
    ((arithmeticChild P a).uniform_parity_comp k (arithmeticChild_uniform_parity P a)
      (generated_contact_constant_parity P k hk))
    ((arithmeticChild P b).uniform_parity_inv (arithmeticChild_uniform_parity P b))

end RegisteredPrime
