module
public import RegisteredPrime.FullPoseHoleCarry
@[expose] public section
namespace RegisteredPrime

/-- Every actual outgoing hole-owner contact in every finite arithmetic
supertile is one of the genuine outer-to-central sibling normals. -/
theorem finite_hole_owner_is_seed (P : Parameters) (n : Nat) (q r : Pose P.p)
    (hq : Descendant P n (identityPose P.p) q)
    (hr : Descendant P n (identityPose P.p) r)
    (hown : Occupies r (hole q)) : OutgoingSeed P (q.relative r) := by
  induction n generalizing q r with
  | zero =>
    have hs : q.Same r := Pose.Same.trans (Pose.Same.symm hq) hr
    exact False.elim (not_occupies_hole q (hs.symm.occupies _ hown))
  | succ n ih =>
    obtain ⟨u, a, hu, hqa⟩ := (descendant_succ_iff P n _ q).mp hq
    obtain ⟨v, b, hv, hrb⟩ := (descendant_succ_iff P n _ r).mp hr
    have heq := hqa.eq
    have her := hrb.eq
    subst q
    subst r
    cases a with
    | outer A hA =>
      have hc := outer_leaf_owner_is_centre P n (identityPose P.p) u (refine P v b) A hA hu hr hown
      rw [← hc.eq]
      change OutgoingSeed P (((doubleAnchor u).comp (arithmeticChild P (.outer A hA))).relative
        ((doubleAnchor u).comp (arithmeticChild P .central)))
      rw [Pose.relative_left_cancel]
      exact ⟨A, hA, rfl⟩
    | central =>
      have hcoarse := central_leaf_owner_parent P u v b hown
      obtain ⟨A, hA, hs⟩ := ih u v hu hv hcoarse
      let role := Role.outer (scalarRole P A) (scalarRole_proper P A hA)
      have hcandidate : Descendant P (n + 1) (identityPose P.p) (refine P v role) :=
        (descendant_succ_iff P n _ _).mpr ⟨v, role, hv, Pose.Same.refl _⟩
      have hcandidateOwn : Occupies (refine P v role) (hole (refine P u .central)) := by
        change Occupies (refine P v (.outer (scalarRole P A) (scalarRole_proper P A hA))) _
        rw [seed_carry_owner P u v A hA hs]
        exact posed_H0_owns_hole P _
      have he := finite_supertile_unique_owner P (n + 1) (identityPose P.p)
        (refine P v role) (refine P v b) hcandidate hr _ hcandidateOwn hown
      rw [← he.eq]
      change OutgoingSeed P ((refine P u .central).relative
        (refine P v (.outer (scalarRole P A) (scalarRole_proper P A hA))))
      rw [seed_carry_owner P u v A hA hs, Pose.relative_comp]
      exact H0_is_seed P

theorem hole_comp {p : Nat} (q r : Pose p) : hole (q.comp r) = q.cell (hole r) := by
  unfold hole
  rw [Pose.comp_cell]

theorem Pose.relative_reverse {p : Nat} (q r : Pose p) : (q.relative r).inv = r.relative q := by
  unfold Pose.relative
  rw [Pose.inv_compose, Pose.inv_inv]

theorem seed_inverse_incoming (P : Parameters) (B : Mask P.p) (hB : Proper B) :
    (outgoingSeed P B hB).inv =
      incomingPose P (scalarRole P B) (scalarRole_proper P B hB) := by
  have hmask : incomingRole P (scalarRole P B) = B := by
    funext i
    exact scalarRole_at P B i
  unfold outgoingSeed incomingPose
  rw [Pose.relative_reverse]
  simp only [hmask]

/-- Full incoming-frame exhaustiveness for the independently defined generated
language E, now without any catalog or hierarchy premise. -/
theorem incoming_frame_property (P : Parameters) : IncomingFrameProperty P := by
  intro e he A hA hin
  obtain ⟨n, q, r, hq, hr, _, hnormal⟩ := he
  have heq := hnormal.eq
  subst e
  have htransport : q.cell (hole (q.relative r)) = hole r := by
    rw [← hole_comp, Pose.comp_relative]
  rw [hin.2] at htransport
  have hreverseOwn : Occupies q (hole r) :=
    ⟨fun i => bit (A i), (identity_occupies _).mp (root_owns_role A hA), htransport⟩
  obtain ⟨B, hB, hseed⟩ := finite_hole_owner_is_seed P n r q hr hq hreverseOwn
  have hrev := congrArg Pose.inv hseed
  rw [Pose.relative_reverse, seed_inverse_incoming] at hrev
  have hsupp : IncomingSupport (q.relative r) (scalarRole P B) := by
    rw [hrev]
    exact incoming_support P _ _
  have hrole : A = scalarRole P B := IncomingSupport.role_unique hin hsupp
  have hfull : q.relative r = incomingPose P A hA := by
    simpa only [hrole] using hrev
  rw [hfull]
  exact Pose.Same.refl _

/-- A nonempty actual predecessor forces every prescribed full marked
predecessor, uniformly over the arithmetic prime family. -/
theorem registered_marked_fan (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (hroot : W.tiles (identityPose P.p))
    {A : Mask P.p} (hA : Proper A) (hnA : NonemptyMask A)
    (hin : (normalizedLocalPatch P W hl hroot (generated_wall_property P)).incoming A) :
    ∀ B (hB : Proper B), ∃ q, W.tiles q ∧ q.Same (incomingPose P B hB) :=
  registered_marked_fan_of_incoming_frames P W hl hroot (incoming_frame_property P) hA hnA hin

end RegisteredPrime
