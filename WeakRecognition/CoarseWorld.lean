module
public import WeakRecognition.Parents
public import RegisteredPrime.CoarseWorld
@[expose] public section
namespace RegisteredPrime.WeakRecognition

/-- Only constant parity is required of every actual cross-child contact. -/
def ChildParity (P : Parameters) (t u : Pose P.p) : Prop :=
  ∀ a b : Role P.p,
    FaceContact (t.comp (arithmeticChild P a)) (u.comp (arithmeticChild P b)) →
    ((t.comp (arithmeticChild P a)).relative (u.comp (arithmeticChild P b))).UniformParity

/-- Exact all-child recognition is kept separate from recognition of the
coarse contact itself. -/
def ChildRecognition (P : Parameters) (t u : Pose P.p) : Prop :=
  ∀ a b : Role P.p,
    FaceContact (t.comp (arithmeticChild P a)) (u.comp (arithmeticChild P b)) →
    RecognitionContact P ((t.comp (arithmeticChild P a)).relative
      (u.comp (arithmeticChild P b)))

theorem ChildRecognition.parity (P : Parameters) {t u : Pose P.p}
    (h : ChildRecognition P t u) : ChildParity P t u := fun a b hc => (h a b hc).parity

theorem child_parity_parent_constant_parity (P : Parameters) (t u : Pose P.p)
    (hc : DoubledFaceContact t u) (hl : ChildParity P t u) :
    (t.relative u).UniformParity := by
  obtain ⟨a, b, hab⟩ := doubled_contact_child_witness P t u hc
  rw [← parent_candidate_reconstruction P t u a b]
  unfold parentCandidate
  exact Pose.uniform_parity_comp _ _
    ((arithmeticChild P a).uniform_parity_comp _ (arithmeticChild_uniform_parity P a) (hl a b hab))
    ((arithmeticChild P b).uniform_parity_inv (arithmeticChild_uniform_parity P b))

/-- Actual cross-child parity and doubled-carrier disjointness force even
relative parent anchors, without generated E or recognition assumptions. -/
theorem child_parity_parent_even (P : Parameters) (t u : Pose P.p)
    (hc : DoubledFaceContact t u) (hl : ChildParity P t u) :
    ∀ i, (t.relative u).anchor i % 2 = 0 := by
  obtain ⟨b, hb⟩ := child_parity_parent_constant_parity P t u hc hl
  cases b with
  | false => exact hb
  | true =>
    have hn := t.inv.doubled_face_contact t u hc
    rw [Pose.inv_comp] at hn
    change DoubledFaceContact (identityPose P.p) (t.relative u) at hn
    exact False.elim (odd_offset_doubled_contact_false _ hn hb)

theorem complete_parent_common_cell (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (t u : Pose P.p) (ht : CompleteParent P W t)
    (hu : CompleteParent P W u) (c : Cell P.p)
    (htc : DoubledOccupies t c) (huc : DoubledOccupies u c) : t = u := by
  apply Classical.byContradiction
  intro hne
  exact complete_parent_doubled_disjoint P W hl t u ht hu hne c ⟨htc, huc⟩

/-- Full world coverage propagates the edgewise even alignment to every
recognized complete parent. -/
theorem complete_parents_same_anchor_parity (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (t u : Pose P.p) (ht : CompleteParent P W t)
    (hu : CompleteParent P W u) :
    ∀ i, t.anchor i % 2 = u.anchor i % 2 := by
  let F : Cell P.p → Prop := fun c => ∀ v, CompleteParent P W v → DoubledOccupies v c →
    ∀ i, v.anchor i % 2 = t.anchor i % 2
  have hstart : F (t.cell (fun _ => 0)) := by
    intro v hv hvc i
    have he := complete_parent_common_cell P W hl v t hv ht _ hvc (doubled_parent_origin_cell P t)
    rw [he]
  have hstep : ∀ a b, Adjacent a b → F a → F b := by
    intro a b hab hfa v hv hvb
    obtain ⟨w, hw, hwa⟩ := complete_parent_cover P W hl a
    have hwp := hfa w hw hwa
    by_cases he : w = v
    · subst v
      exact hwp
    · have hc : DoubledFaceContact w v :=
        ⟨complete_parent_doubled_disjoint P W hl w v hw hv he, a, b, hwa, hvb, hab⟩
      have hchild : ChildRecognition P w v := complete_parent_child_recognition P W hl w v hw hv
      have hpar := relative_even_same_anchor_parity w v
        (child_parity_parent_even P w v hc (hchild.parity P))
      intro i
      exact (hpar i).symm.trans (hwp i)
  have h := cell_property_global F hstep _ hstart (u.cell (fun _ => 0))
  intro i
  exact (h u hu (doubled_parent_origin_cell P u) i).symm

theorem complete_parents_relative_even (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (t u : Pose P.p) (ht : CompleteParent P W t)
    (hu : CompleteParent P W u) : ∀ i, (t.relative u).anchor i % 2 = 0 :=
  same_anchor_parity_relative_even t u (complete_parents_same_anchor_parity P W hl t u ht hu)

theorem ChildRecognition.reframe (P : Parameters) (g t u : Pose P.p)
    (hl : ChildRecognition P t u) : ChildRecognition P (g.comp t) (g.comp u) := by
  intro a b hc
  have hc' : FaceContact (t.comp (arithmeticChild P a)) (u.comp (arithmeticChild P b)) := by
    have h := g.inv.face_contact _ _ hc
    simpa only [← Pose.comp_assoc, Pose.inv_comp, Pose.identity_comp] using h
  rw [Pose.comp_assoc, Pose.comp_assoc, Pose.relative_left_cancel]
  exact hl a b hc'

/-- Exact geometric parent contact plus every actual cross-child recognition
condition. This is not RecognitionContact of the parent. -/
def CoarseContact (P : Parameters) (e : Pose P.p) : Prop :=
  DoubledFaceContact (identityPose P.p) (doubleAnchor e) ∧
  ChildRecognition P (identityPose P.p) (doubleAnchor e)

theorem complete_parent_coarse_contact (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (t u : Pose P.p) (ht : CompleteParent P W t)
    (hu : CompleteParent P W u) (hc : DoubledFaceContact t u) :
    CoarseContact P (halfAnchor (t.relative u)) := by
  have hchild : ChildRecognition P t u := complete_parent_child_recognition P W hl t u ht hu
  have he := child_parity_parent_even P t u hc (hchild.parity P)
  unfold CoarseContact
  rw [double_halfAnchor _ he]
  constructor
  · have h := t.inv.doubled_face_contact t u hc
    rwa [Pose.inv_comp] at h
  · have h := ChildRecognition.reframe P t.inv t u hchild
    rwa [Pose.inv_comp] at h

/-- The actual normalized coarse world. Its coverage and nonoverlap are
proved from weak recognition, not assumed as coarsening data. -/
noncomputable def coarsenAt (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (t : Pose P.p) (ht : CompleteParent P W t) : RegisteredWorld P.p where
  tiles := fun q => CompleteParent P W (t.comp (doubleAnchor q))
  covers := by
    intro c
    let x : Cell P.p := fun i => 2 * c i
    have hxf : floorCell x = c := by
      funext i
      change (2 * c i) / 2 = c i
      omega
    obtain ⟨u, hu, huc⟩ := complete_parent_cover P W hl (t.cell x)
    have he := complete_parents_relative_even P W hl t u ht hu
    let q := halfAnchor (t.relative u)
    have hq : t.comp (doubleAnchor q) = u := by
      rw [double_halfAnchor _ he, Pose.comp_relative]
    refine ⟨q, ?_, ?_⟩
    · rwa [hq]
    · have hd : DoubledOccupies (doubleAnchor q) x :=
        (doubled_occupies_comp_cell t (doubleAnchor q) x).mp (hq ▸ huc)
      have ho := (doubled_doubleAnchor_iff q x).mp hd
      rwa [hxf] at ho
  nonoverlap := by
    intro q r hq hr c hqc hrc
    let x : Cell P.p := fun i => 2 * c i
    have hxf : floorCell x = c := by
      funext i
      change (2 * c i) / 2 = c i
      omega
    have hqx : DoubledOccupies (doubleAnchor q) x :=
      (doubled_doubleAnchor_iff q x).mpr (hxf ▸ hqc)
    have hrx : DoubledOccupies (doubleAnchor r) x :=
      (doubled_doubleAnchor_iff r x).mpr (hxf ▸ hrc)
    have he := complete_parent_common_cell P W hl _ _ hq hr (t.cell x)
      ((doubled_occupies_comp_cell t (doubleAnchor q) x).mpr hqx)
      ((doubled_occupies_comp_cell t (doubleAnchor r) x).mpr hrx)
    have hqr := doubleAnchor_injective q r (Pose.comp_left_cancel t _ _ he)
    subst r
    exact Pose.Same.refl _

theorem coarsenAt_parent_surjective (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (t : Pose P.p) (ht : CompleteParent P W t)
    (u : Pose P.p) (hu : CompleteParent P W u) :
    ∃ q, (coarsenAt P W hl t ht).tiles q ∧ t.comp (doubleAnchor q) = u := by
  have he := complete_parents_relative_even P W hl t u ht hu
  let q := halfAnchor (t.relative u)
  have hq : t.comp (doubleAnchor q) = u := by
    rw [double_halfAnchor _ he, Pose.comp_relative]
  refine ⟨q, ?_, hq⟩
  change CompleteParent P W (t.comp (doubleAnchor q))
  rwa [hq]

/-- Exact reconstruction of the full marked fine tile set. -/
theorem coarsenAt_reconstruct (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (t : Pose P.p) (ht : CompleteParent P W t) (q : Pose P.p) :
    W.tiles q ↔ ∃ r, (coarsenAt P W hl t ht).tiles r ∧
      ∃ a : Role P.p, q = t.comp (refine P r a) := by
  constructor
  · intro hq
    obtain ⟨u, hu, ⟨a, ha⟩, _⟩ := registered_unique_parent_pose P W hl q hq
    obtain ⟨r, hr, he⟩ := coarsenAt_parent_surjective P W hl t ht u hu
    refine ⟨r, hr, a, ?_⟩
    rw [ha, ← he, Pose.comp_assoc]
    rfl
  · rintro ⟨r, hr, a, ha⟩
    rw [ha]
    have h := hr a
    rwa [Pose.comp_assoc] at h

def CoarseLegal (P : Parameters) (W : RegisteredWorld P.p) : Prop :=
  ∀ q r, W.tiles q → W.tiles r → FaceContact q r → CoarseContact P (q.relative r)

theorem coarsenAt_coarse_legal (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (t : Pose P.p) (ht : CompleteParent P W t) :
    CoarseLegal P (coarsenAt P W hl t ht) := by
  intro q r hq hr hc
  have hd := t.doubled_face_contact _ _ (face_contact_doubled q r hc)
  have h := complete_parent_coarse_contact P W hl _ _ hq hr hd
  rw [Pose.relative_left_cancel, ← doubleAnchor_relative, half_doubleAnchor] at h
  exact h

/-- A weakly recognition-legal world always has a concrete full coarse world
with exact all-child recognition. Parent-contact recognition is not assumed
or concluded, and remains the separate closure obligation. -/
theorem registered_coarse_world_exists (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) : ∃ V : RegisteredWorld P.p, CoarseLegal P V := by
  obtain ⟨t, ht, _⟩ := complete_parent_cover P W hl (fun _ => 0)
  exact ⟨coarsenAt P W hl t ht, coarsenAt_coarse_legal P W hl t ht⟩

end RegisteredPrime.WeakRecognition
