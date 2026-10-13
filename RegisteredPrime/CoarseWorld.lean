module
public import RegisteredPrime.GlobalParentAlignment
@[expose] public section
namespace RegisteredPrime

theorem doubled_doubleAnchor_iff {p : Nat} (q : Pose p) (c : Cell p) :
    DoubledOccupies (doubleAnchor q) c ↔ Occupies q (floorCell c) := by
  unfold DoubledOccupies
  rw [← doubleAnchor_inv, doubled_iff_unit_floor, doubleAnchor_cell_floor,
    ← occupies_inverse_iff]

@[simp] theorem half_doubleAnchor {p : Nat} (q : Pose p) : halfAnchor (doubleAnchor q) = q := by
  apply Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, fun i => ?_⟩
  change (2 * q.anchor i) / 2 = q.anchor i
  omega

theorem doubleAnchor_injective {p : Nat} (q r : Pose p) (h : doubleAnchor q = doubleAnchor r) :
    q = r := by
  have he := congrArg (@halfAnchor p) h
  simpa using he

theorem doubleAnchor_relative {p : Nat} (q r : Pose p) :
    doubleAnchor (q.relative r) = (doubleAnchor q).relative (doubleAnchor r) := by
  unfold Pose.relative
  rw [doubleAnchor_comp, doubleAnchor_inv]

def doubledCell {p : Nat} (c : Cell p) (j : Fin p) (upper : Bool) : Cell p :=
  fun i => 2 * c i + if i = j then bit upper else 0

@[simp] theorem doubledCell_floor {p : Nat} (c : Cell p) (j : Fin p) (upper : Bool) :
    floorCell (doubledCell c j upper) = c := by
  funext i
  unfold floorCell doubledCell
  by_cases hij : i = j <;> cases upper <;> simp [hij, bit] <;> omega

theorem adjacent_doubled_cells {p : Nat} (a b : Cell p) (hab : Adjacent a b) :
    ∃ x y, floorCell x = a ∧ floorCell y = b ∧ Adjacent x y := by
  obtain ⟨j, hj, ht⟩ := hab
  rcases hj with hj | hj
  · refine ⟨doubledCell a j false, doubledCell b j true,
      doubledCell_floor _ _ _, doubledCell_floor _ _ _, j, Or.inl ?_, ?_⟩
    · simp [doubledCell, bit]
      omega
    · intro i hij
      simp [doubledCell, hij, ht i hij]
  · refine ⟨doubledCell a j true, doubledCell b j false,
      doubledCell_floor _ _ _, doubledCell_floor _ _ _, j, Or.inr ?_, ?_⟩
    · simp [doubledCell, bit]
      omega
    · intro i hij
      simp [doubledCell, hij, ht i hij]

theorem face_contact_doubled {p : Nat} (q r : Pose p) (hc : FaceContact q r) :
    DoubledFaceContact (doubleAnchor q) (doubleAnchor r) := by
  obtain ⟨hd, a, b, ha, hb, hab⟩ := hc
  constructor
  · intro c ⟨hqc, hrc⟩
    exact hd (floorCell c) ⟨(doubled_doubleAnchor_iff q c).mp hqc,
      (doubled_doubleAnchor_iff r c).mp hrc⟩
  · obtain ⟨x, y, hx, hy, hxy⟩ := adjacent_doubled_cells a b hab
    refine ⟨x, y, (doubled_doubleAnchor_iff q x).mpr ?_,
      (doubled_doubleAnchor_iff r y).mpr ?_, hxy⟩
    · rwa [hx]
    · rwa [hy]

/-- Normalize, rotate and divide the actual complete parents by two. Coverage
and nonoverlap are proved fields; no legality or hierarchy field is assumed. -/
noncomputable def RegisteredWorld.coarsenAt (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (t : Pose P.p) (ht : CompleteParent P W t) : RegisteredWorld P.p where
  tiles := fun q => CompleteParent P W (t.comp (doubleAnchor q))
  covers := by
    intro c
    let x : Cell P.p := fun i => 2 * c i
    have hxf : floorCell x = c := by
      funext i
      change (2 * c i) / 2 = c i
      omega
    obtain ⟨u, hu, huc⟩ := complete_parent_cell_cover P W hl (t.cell x)
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

/-- Every actual complete parent appears in the normalized coarse world. -/
theorem RegisteredWorld.coarsenAt_parent_surjective (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (t : Pose P.p) (ht : CompleteParent P W t)
    (u : Pose P.p) (hu : CompleteParent P W u) :
    ∃ q, (W.coarsenAt P hl t ht).tiles q ∧ t.comp (doubleAnchor q) = u := by
  have he := complete_parents_relative_even P W hl t u ht hu
  let q := halfAnchor (t.relative u)
  have hq : t.comp (doubleAnchor q) = u := by
    rw [double_halfAnchor _ he, Pose.comp_relative]
  refine ⟨q, ?_, hq⟩
  change CompleteParent P W (t.comp (doubleAnchor q))
  rwa [hq]

/-- Exact reconstruction of the full marked tile set from the actual coarse
world and the prescribed arithmetic subdivision. -/
theorem RegisteredWorld.coarsenAt_reconstruct (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (t : Pose P.p) (ht : CompleteParent P W t) (q : Pose P.p) :
    W.tiles q ↔ ∃ r, (W.coarsenAt P hl t ht).tiles r ∧
      ∃ a : Role P.p, q = t.comp (refine P r a) := by
  constructor
  · intro hq
    obtain ⟨u, hu, a, ha⟩ := registered_complete_parent_pose P W hl q hq
    obtain ⟨r, hr, he⟩ := W.coarsenAt_parent_surjective P hl t ht u hu
    refine ⟨r, hr, a, ?_⟩
    rw [ha, ← he, Pose.comp_assoc]
    rfl
  · rintro ⟨r, hr, a, ha⟩
    rw [ha]
    have h := hr a
    rwa [Pose.comp_assoc] at h

/-- The actual coarse language is retained explicitly instead of identified
with the generated language. -/
def RegisteredWorld.CoarseLegal (P : Parameters) (W : RegisteredWorld P.p) : Prop :=
  ∀ q r, W.tiles q → W.tiles r → FaceContact q r → CoarseContact P (q.relative r)

theorem RegisteredWorld.coarsenAt_coarse_legal (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (t : Pose P.p) (ht : CompleteParent P W t) :
    (W.coarsenAt P hl t ht).CoarseLegal P := by
  intro q r hq hr hc
  have hd := t.doubled_face_contact _ _ (face_contact_doubled q r hc)
  have h := CompleteParent.coarse_contact P W hl _ _ hq hr hd
  rw [Pose.relative_left_cancel, ← doubleAnchor_relative, half_doubleAnchor] at h
  exact h

/-- Every full E-legal world admits an actual registered coarse world whose
face contacts satisfy the exact all-children CL(E) predicate. E-closure remains
a separate theorem and is not a hypothesis hidden inside the output. -/
theorem registered_coarse_world_exists (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) : ∃ V : RegisteredWorld P.p, V.CoarseLegal P := by
  obtain ⟨t, ht, _⟩ := complete_parent_cell_cover P W hl (fun _ => 0)
  exact ⟨W.coarsenAt P hl t ht, W.coarsenAt_coarse_legal P hl t ht⟩

end RegisteredPrime
