module
public import WeakRecognition.Contact
@[expose] public section
namespace RegisteredPrime.WeakRecognition

theorem root_local_incoming_of_support (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (hroot : W.tiles (identityPose P.p)) (q : Pose P.p)
    (hq : W.tiles q) (A : Mask P.p) (hA : Proper A) (hs : IncomingSupport q A) :
    (worldLocalPatch P W hl (identityPose P.p) hroot).incoming A := by
  let j : Fin P.p := ⟨0, by have := P.prime.two_le; omega⟩
  have hface := exterior_owner_face_contact W hroot A hA j q hq
    (incoming_owns_exterior q A hs j)
  refine ⟨q, ⟨?_, hface⟩, hs⟩
  change W.tiles ((identityPose P.p).comp q)
  rwa [Pose.identity_comp]

/-- The two actual H0 candidate stars cannot both remain incomplete under
only the explicit recognition contact clauses. -/
theorem H0_incomplete_contradiction (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (hroot : W.tiles (identityPose P.p)) (hH0 : W.tiles (H0Pose P.p))
    (hnroot : ¬ CompleteStar P W (identityPose P.p))
    (hnH0 : ¬ CompleteStar P W (H0Pose P.p)) : False := by
  let L := worldLocalPatch P W hl (H0Pose P.p) hH0
  have he : L.incoming (fun _ => false) := by
    apply local_incoming_of_pose P W hl (H0Pose P.p) hH0 (fun _ => false) (empty_proper P)
    rw [H0_comp_empty_incoming]
    exact hroot
  have hinc : ¬ ∀ A, Proper A → L.incoming A := local_incomplete P W hl _ hH0 hnH0
  let j : Fin P.p := ⟨0, by have := P.prime.two_le; omega⟩
  obtain ⟨q, hq, hb⟩ := L.fanData.incomplete_all_walls (P.prime.three_le P.odd) hinc j false
  have hh := negative_wall_hole_with_empty L he q hq j hb
  have hs := H0_negative_wall_incoming q j hb hh
  have hm : W.tiles ((H0Pose P.p).comp q) := hq.1
  have hin := root_local_incoming_of_support P W hl hroot _ hm (complementAxis j)
    (complementAxis_proper j) hs
  exact hnroot (completeStar_of_incoming P W hl _ hroot (complementAxis_proper j)
    (complementAxis_nonempty (P.prime.three_le P.odd) j) hin)

theorem root_parent_alternative (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (hroot : W.tiles (identityPose P.p)) :
    CompleteStar P W (identityPose P.p) ∨ CompleteStar P W (W.owner (identityPose P.p)) := by
  classical
  obtain ⟨A, hA, hs⟩ := owner_seed P W hl _ hroot
  by_cases hnA : NonemptyMask A
  · exact Or.inr (owner_star_of_nonempty_role P W hl _ hroot A hA hnA hs)
  · have hA0 : A = fun _ => false := by
      funext i
      cases hi : A i
      · rfl
      · exact False.elim (hnA ⟨i, hi⟩)
    subst A
    have hseed0 : outgoingSeed P (fun _ => false) hA = H0Pose P.p := empty_outgoing_is_H0 P
    have howner : W.owner (identityPose P.p) = H0Pose P.p :=
      (relative_identity_same _).eq.symm.trans (hs.trans hseed0)
    by_cases hrootStar : CompleteStar P W (identityPose P.p)
    · exact Or.inl hrootStar
    · right
      rw [howner]
      apply Classical.byContradiction
      intro h
      have hm : W.tiles (H0Pose P.p) := howner ▸ W.owner_mem (identityPose P.p)
      exact H0_incomplete_contradiction P W hl hroot hm hrootStar h

/-- Exact geometric overlap exclusion is reused unchanged. -/
theorem stars_not_both_complete (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (q : Pose P.p) (hq : W.tiles q)
    (hsq : CompleteStar P W q) (hso : CompleteStar P W (W.owner q)) : False := by
  obtain ⟨A, hA, hs⟩ := owner_seed P W hl q hq
  obtain ⟨t, htq, hto⟩ := outgoing_seed_factorization P q (W.owner q) A hA hs
  have hq' : (W.reframe t).tiles (arithmeticChild P (.outer A hA)) := by
    change W.tiles (t.comp (arithmeticChild P (.outer A hA)))
    rwa [htq]
  have ho' : (W.reframe t).tiles (arithmeticChild P .central) := by
    change W.tiles (t.comp (arithmeticChild P .central))
    rw [hto]
    exact W.owner_mem q
  have hsq' : CompleteStar P (W.reframe t) (arithmeticChild P (.outer A hA)) := by
    apply (CompleteStar.reframe_iff P W t _).mpr
    rwa [htq]
  have hso' : CompleteStar P (W.reframe t) (arithmeticChild P .central) := by
    apply (CompleteStar.reframe_iff P W t _).mpr
    rwa [hto]
  exact standard_stars_not_both P (W.reframe t) A hA hq' ho' hsq' hso'

theorem complete_parent_exists (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (q : Pose P.p) (hq : W.tiles q) :
    ∃ c : Pose P.p, W.tiles c ∧ CompleteStar P W c ∧ ParentContains P c q := by
  let V := W.reframe q
  have hV : Legal P V := reframe_legal P W hl q
  have hroot : V.tiles (identityPose P.p) := W.reframe_root q hq
  rcases root_parent_alternative P V hV hroot with hs | hs
  · refine ⟨q, hq, ?_, Or.inl rfl⟩
    have ht := (CompleteStar.reframe_iff P W q (identityPose P.p)).mp hs
    rwa [Pose.comp_identity] at ht
  · let c := V.owner (identityPose P.p)
    have hc : V.tiles c := V.owner_mem (identityPose P.p)
    have hs' : CompleteStar P W (q.comp c) := (CompleteStar.reframe_iff P W q c).mp hs
    obtain ⟨A, hA, hseed⟩ := owner_seed P V hV _ hroot
    have hm := owner_incoming_pose P V (identityPose P.p) A hA hseed
    have he : (q.comp c).comp
        (incomingPose P (scalarRole P A) (scalarRole_proper P A hA)) = q := by
      rw [Pose.comp_assoc]
      change q.comp ((V.owner (identityPose P.p)).comp
        (incomingPose P (scalarRole P A) (scalarRole_proper P A hA))) = q
      rw [hm, Pose.comp_identity]
    exact ⟨q.comp c, hc, hs', Or.inr ⟨scalarRole P A, scalarRole_proper P A hA, he.symm⟩⟩

/-- Unique full marked parent recognition from explicit contact conditions,
coverage, and nonoverlap, with no E-legality or hierarchy premise. -/
theorem registered_unique_parent (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (q : Pose P.p) (hq : W.tiles q) :
    ∃ c : Pose P.p, W.tiles c ∧ CompleteStar P W c ∧ ParentContains P c q ∧
      ∀ d : Pose P.p, W.tiles d → CompleteStar P W d → ParentContains P d q → d = c := by
  obtain ⟨c, hc, hsc, hmc⟩ := complete_parent_exists P W hl q hq
  refine ⟨c, hc, hsc, hmc, ?_⟩
  intro d hd hsd hmd
  rcases parent_centre_candidates P W c q hc hmc with hcq | hco <;>
    rcases parent_centre_candidates P W d q hd hmd with hdq | hdo
  · exact hdq.trans hcq.symm
  · have hsq : CompleteStar P W q := hcq ▸ hsc
    have hso : CompleteStar P W (W.owner q) := hdo ▸ hsd
    exact False.elim (stars_not_both_complete P W hl q hq hsq hso)
  · have hsq : CompleteStar P W q := hdq ▸ hsd
    have hso : CompleteStar P W (W.owner q) := hco ▸ hsc
    exact False.elim (stars_not_both_complete P W hl q hq hsq hso)
  · exact hdo.trans hco.symm

theorem complete_stars_disjoint (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (c d q : Pose P.p) (hc : W.tiles c) (hd : W.tiles d)
    (hsc : CompleteStar P W c) (hsd : CompleteStar P W d)
    (hcq : ParentContains P c q) (hdq : ParentContains P d q) : c = d := by
  have hq : W.tiles q := by
    rcases hcq with he | ⟨A, hA, he⟩
    · exact he ▸ hc
    · rw [he]
      exact hsc A hA
  obtain ⟨e, _, _, _, hu⟩ := registered_unique_parent P W hl q hq
  exact (hu c hc hsc hcq).trans (hu d hd hsd hdq).symm

/-- Unique recognition of the actual unscaled doubled-parent pose for the
weaker local language, retaining every signed coordinate-frame component. -/
theorem registered_unique_parent_pose (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (q : Pose P.p) (hq : W.tiles q) :
    ∃ t : Pose P.p, CompleteParent P W t ∧ ParentChild P t q ∧
      ∀ u : Pose P.p, CompleteParent P W u → ParentChild P u q → u = t := by
  obtain ⟨c, hc, hsc, hmc, hu⟩ := registered_unique_parent P W hl q hq
  refine ⟨centerParent P c, completeStar_completeParent P W c hc hsc,
    parentContains_parentChild P c q hmc, ?_⟩
  intro u hpu hcu
  have he : u.comp (arithmeticChild P .central) = c := hu _ (hpu .central)
    (completeParent_completeStar P W u hpu) (parentChild_parentContains P u q hcu)
  calc
    u = centerParent P (u.comp (arithmeticChild P .central)) := (centerParent_of_parent P u).symm
    _ = centerParent P c := congrArg (centerParent P) he

/-- The recognized doubled parents cover every actual integer cell. -/
theorem complete_parent_cover (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (c : Cell P.p) :
    ∃ t : Pose P.p, CompleteParent P W t ∧ DoubledOccupies t c := by
  obtain ⟨q, hq, hqc⟩ := W.covers c
  obtain ⟨t, ht, ⟨a, ha⟩, _⟩ := registered_unique_parent_pose P W hl q hq
  rw [ha] at hqc
  exact ⟨t, ht, (doubled_occupies_iff_child P t c).mpr ⟨a, hqc⟩⟩

/-- Distinct recognized parents are disjoint as whole doubled chairs. -/
theorem complete_parent_doubled_disjoint (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (t u : Pose P.p) (ht : CompleteParent P W t)
    (hu : CompleteParent P W u) (hne : t ≠ u) : DoubledDisjoint t u := by
  intro c ⟨htc, huc⟩
  obtain ⟨a, ha⟩ := (doubled_occupies_iff_child P t c).mp htc
  obtain ⟨b, hb⟩ := (doubled_occupies_iff_child P u c).mp huc
  have he := (W.nonoverlap _ _ (ht a) (hu b) c ha hb).eq
  obtain ⟨v, _, _, hv⟩ := registered_unique_parent_pose P W hl _ (ht a)
  have htv := hv t ht ⟨a, rfl⟩
  have huv := hv u hu ⟨b, he⟩
  exact hne (htv.trans huv.symm)

/-- Every actual contact across complete parents inherits the explicit weak
contact predicate; no claim about the coarse contact is made here. -/
theorem complete_parent_child_recognition (P : Parameters) (W : RegisteredWorld P.p)
    (hl : Legal P W) (t u : Pose P.p) (ht : CompleteParent P W t) (hu : CompleteParent P W u) :
    ∀ a b : Role P.p,
      FaceContact (t.comp (arithmeticChild P a)) (u.comp (arithmeticChild P b)) →
      RecognitionContact P ((t.comp (arithmeticChild P a)).relative
        (u.comp (arithmeticChild P b))) := by
  intro a b hc
  exact hl _ _ (ht a) (hu b) hc

end RegisteredPrime.WeakRecognition
