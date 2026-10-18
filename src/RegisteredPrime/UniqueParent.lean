module
public import RegisteredPrime.ParentOverlapExclusion
@[expose] public section
namespace RegisteredPrime

/-- Concrete child membership in the star centred at c. -/
def ParentContains (P : Parameters) (c q : Pose P.p) : Prop :=
  q = c ∨ ∃ A, ∃ hA : Proper A, q = c.comp (incomingPose P A hA)

/-- Any actual candidate parent containing q has centre q or the actual owner
of q's missing cell. This follows from cell ownership, not recognizability. -/
theorem parent_centre_candidates (P : Parameters) (W : RegisteredWorld P.p)
    (c q : Pose P.p) (hc : W.tiles c) (hm : ParentContains P c q) :
    c = q ∨ c = W.owner q := by
  rcases hm with he | ⟨A, hA, he⟩
  · exact Or.inl he.symm
  · right
    have hown : Occupies c (hole q) := by
      rw [he, hole_comp, (incoming_support P A hA).2]
      exact ⟨fun i => bit (A i), (identity_occupies _).mp (root_owns_role A hA), rfl⟩
    exact (W.nonoverlap c (W.owner q) hc (W.owner_mem q) _ hown (W.owner_occupies q)).eq

/-- Every actual tile has a complete full marked parent star. -/
theorem complete_parent_exists (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (q : Pose P.p) (hq : W.tiles q) :
    ∃ c : Pose P.p, W.tiles c ∧ CompleteStar P W c ∧ ParentContains P c q := by
  let V := W.reframe q
  have hV : V.Legal P := W.reframe_legal P hl q
  have hroot : V.tiles (identityPose P.p) := W.reframe_root q hq
  rcases root_parent_alternative P V hV hroot with hs | hs
  · refine ⟨q, hq, ?_, Or.inl rfl⟩
    have ht := (CompleteStar.reframe_iff P W q (identityPose P.p)).mp hs
    rwa [Pose.comp_identity] at ht
  · let c := V.owner (identityPose P.p)
    have hc : V.tiles c := V.owner_mem _
    have hs' : CompleteStar P W (q.comp c) := (CompleteStar.reframe_iff P W q c).mp hs
    obtain ⟨A, hA, hseed⟩ := V.owner_seed P hV _ hroot
    have hm := owner_incoming_pose P V (identityPose P.p) A hA hseed
    have he : (q.comp c).comp
        (incomingPose P (scalarRole P A) (scalarRole_proper P A hA)) = q := by
      rw [Pose.comp_assoc]
      change q.comp ((V.owner (identityPose P.p)).comp
        (incomingPose P (scalarRole P A) (scalarRole_proper P A hA))) = q
      rw [hm, Pose.comp_identity]
    exact ⟨q.comp c, hc, hs', Or.inr ⟨scalarRole P A, scalarRole_proper P A hA, he.symm⟩⟩

/-- Uniform first-level unique marked-parent recognition in every full registered
E-legal world. Parent existence, exact membership and exclusivity are all proved. -/
theorem registered_unique_parent (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (q : Pose P.p) (hq : W.tiles q) :
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

/-- Distinct complete parent stars share no actual tile. -/
theorem complete_stars_disjoint (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (c d q : Pose P.p) (hc : W.tiles c) (hd : W.tiles d)
    (hsc : CompleteStar P W c) (hsd : CompleteStar P W d)
    (hcq : ParentContains P c q) (hdq : ParentContains P d q) : c = d := by
  have hq : W.tiles q := by
    rcases hcq with he | ⟨A, hA, he⟩
    · exact he ▸ hc
    · rw [he]
      exact hsc A hA
  obtain ⟨e, _, _, _, hu⟩ := registered_unique_parent P W hl q hq
  exact (hu c hc hsc hcq).trans (hu d hd hsd hdq).symm

/-- Complete doubled parents are concrete images of every prescribed child. -/
def CompleteParent (P : Parameters) (W : RegisteredWorld P.p) (t : Pose P.p) : Prop :=
  ∀ a : Role P.p, W.tiles (t.comp (arithmeticChild P a))

def ParentChild (P : Parameters) (t q : Pose P.p) : Prop :=
  ∃ a : Role P.p, q = t.comp (arithmeticChild P a)

theorem completeStar_completeParent (P : Parameters) (W : RegisteredWorld P.p)
    (c : Pose P.p) (hc : W.tiles c) (hs : CompleteStar P W c) :
    CompleteParent P W (centerParent P c) := CompleteStar.child_mem P W c hc hs

theorem parentContains_parentChild (P : Parameters) (c q : Pose P.p)
    (h : ParentContains P c q) : ParentChild P (centerParent P c) q := by
  rcases h with he | ⟨A, hA, he⟩
  · exact ⟨.central, he.trans (centerParent_central P c).symm⟩
  · refine ⟨.outer (incomingRole P A) (incomingRole_proper P A hA), ?_⟩
    rw [he]
    unfold centerParent incomingPose Pose.relative
    rw [Pose.comp_assoc]

/-- Every tile lies in an actual complete doubled arithmetic parent. -/
theorem registered_complete_parent_pose (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (q : Pose P.p) (hq : W.tiles q) :
    ∃ t : Pose P.p, CompleteParent P W t ∧ ParentChild P t q := by
  obtain ⟨c, hc, hs, hm⟩ := complete_parent_exists P W hl q hq
  exact ⟨centerParent P c, completeStar_completeParent P W c hc hs, parentContains_parentChild P c q hm⟩

@[simp] theorem centerParent_of_parent (P : Parameters) (t : Pose P.p) :
    centerParent P (t.comp (arithmeticChild P .central)) = t := by
  unfold centerParent
  rw [Pose.comp_assoc, Pose.comp_inv, Pose.comp_identity]

theorem completeParent_completeStar (P : Parameters) (W : RegisteredWorld P.p)
    (t : Pose P.p) (ht : CompleteParent P W t) :
    CompleteStar P W (t.comp (arithmeticChild P .central)) := by
  intro A hA
  change W.tiles ((t.comp (arithmeticChild P .central)).comp
    ((arithmeticChild P .central).relative
      (arithmeticChild P (.outer (incomingRole P A) (incomingRole_proper P A hA)))))
  rw [Pose.comp_assoc, Pose.comp_relative]
  exact ht _

theorem parentChild_parentContains (P : Parameters) (t q : Pose P.p)
    (h : ParentChild P t q) : ParentContains P (t.comp (arithmeticChild P .central)) q := by
  obtain ⟨a, ha⟩ := h
  cases a with
  | central => exact Or.inl ha
  | outer A hA =>
    refine Or.inr ⟨scalarRole P A, scalarRole_proper P A hA, ?_⟩
    rw [← central_relative_outer_incoming, Pose.comp_assoc, Pose.comp_relative]
    exact ha

/-- Uniform unique recognition of the actual unscaled doubled-parent pose,
not just a choice of a support or an unsigned-frame class. -/
theorem registered_unique_parent_pose (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (q : Pose P.p) (hq : W.tiles q) :
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

end RegisteredPrime
