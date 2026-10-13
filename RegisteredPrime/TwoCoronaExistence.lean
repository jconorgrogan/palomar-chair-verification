module
public import RegisteredPrime.WorldHoleOwners
@[expose] public section
namespace RegisteredPrime

theorem incoming_empty_is_H0_inverse (P : Parameters) :
    incomingPose P (fun _ => false) (empty_proper P) = (H0Pose P.p).inv := by
  have h := seed_inverse_incoming P (fun _ => false) (empty_proper P)
  rw [empty_outgoing_is_H0] at h
  have he : scalarRole P (fun _ => false) = fun _ => false := rfl
  simpa only [he] using h.symm

theorem H0_comp_empty_incoming (P : Parameters) :
    (H0Pose P.p).comp (incomingPose P (fun _ => false) (empty_proper P)) = identityPose P.p := by
  rw [incoming_empty_is_H0_inverse, Pose.comp_inv]

/-- An empty predecessor forces every present negative wall to omit -e_j.
This is a concrete nonoverlap calculation, not a two-corona hypothesis. -/
theorem negative_wall_hole_with_empty {p : Nat} (L : LocalPatch p)
    (he : L.incoming (fun _ => false)) (q : Pose p) (hq : L.tiles q) (j : Fin p)
    (hbox : boxLower q = wallBox j false) : hole q = fun i => -unitAxis j i := by
  obtain ⟨r, hr, hri⟩ := he
  have hx : Occupies r (fun i => -unitAxis j i) := by
    have h := incoming_owns_exterior r (fun _ => false) hri j
    have hext : exterior (fun _ : Fin p => false) j = fun i => -unitAxis j i := by
      funext i
      by_cases hi : i = j <;> simp [exterior, bit, unitAxis, hi]
    rwa [hext] at h
  apply Classical.byContradiction
  intro hn
  have hqx : Occupies q (fun i => -unitAxis j i) := by
    apply (occupies_box_iff q _).mpr
    constructor
    · intro i
      rw [congrFun hbox i]
      by_cases hi : i = j <;> simp [wallBox, unitAxis, hi]
    · exact fun h => hn h.symm
  have hs := L.nonoverlap r q hr hq _ hx hqx
  have hb := congrFun (hri.1.symm.trans (hs.boxLower.trans hbox)) j
  simp [bit, wallBox] at hb

@[simp] theorem H0_cell {p : Nat} (c : Cell p) (i : Fin p) :
    (H0Pose p).cell c i = 1 + c i := by
  simp [H0Pose, identityPose, Pose.cell, RegisteredFrame.linear, RegisteredFrame.sign, bit]

theorem H0_boxLower {p : Nat} (q : Pose p) (i : Fin p) :
    boxLower ((H0Pose p).comp q) i = 1 + boxLower q i := by
  simp only [boxLower, Pose.comp, RegisteredFrame.comp, RegisteredFrame.linear,
    RegisteredFrame.sign, H0Pose, identityPose]
  simp
  omega

def complementAxis {p : Nat} (j : Fin p) : Mask p := fun i => decide (i ≠ j)

theorem complementAxis_proper {p : Nat} (j : Fin p) : Proper (complementAxis j) :=
  ⟨j, by simp [complementAxis]⟩

theorem complementAxis_nonempty {p : Nat} (hp : 3 ≤ p) (j : Fin p) : NonemptyMask (complementAxis j) := by
  obtain ⟨k, hkj, _⟩ := third_axis hp j j
  exact ⟨k, by simp [complementAxis, hkj]⟩

/-- Moving the negative wall of H0 back to the root gives a nonempty predecessor. -/
theorem H0_negative_wall_incoming {p : Nat} (q : Pose p) (j : Fin p)
    (hb : boxLower q = wallBox j false) (hh : hole q = fun i => -unitAxis j i) :
    IncomingSupport ((H0Pose p).comp q) (complementAxis j) := by
  constructor
  · funext i
    rw [H0_boxLower, congrFun hb i]
    by_cases hi : i = j <;> simp [wallBox, complementAxis, bit, hi]
  · funext i
    rw [hole_comp]
    rw [H0_cell, hh]
    by_cases hi : i = j <;> simp [unitAxis, complementAxis, bit, hi]

theorem root_local_incoming_of_support (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (hroot : W.tiles (identityPose P.p)) (q : Pose P.p)
    (hq : W.tiles q) (A : Mask P.p) (hA : Proper A) (hs : IncomingSupport q A) :
    (worldLocalPatch P W hl (identityPose P.p) hroot).incoming A := by
  let j : Fin P.p := ⟨0, by have := P.prime.two_le; omega⟩
  have hface := exterior_owner_face_contact W hroot A hA j q hq
    (incoming_owns_exterior q A hs j)
  refine ⟨q, ⟨?_, hface⟩, hs⟩
  change W.tiles ((identityPose P.p).comp q)
  rwa [Pose.identity_comp]

/-- The actual H0 pair cannot have two incomplete candidate stars. -/
theorem H0_incomplete_contradiction (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (hroot : W.tiles (identityPose P.p)) (hH0 : W.tiles (H0Pose P.p))
    (hnroot : ¬ CompleteStar P W (identityPose P.p)) (hnH0 : ¬ CompleteStar P W (H0Pose P.p)) : False := by
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

/-- Two actual complete coronas force at least one of the two candidate marked
stars in a full registered E-world. No first-level hierarchy is assumed. -/
theorem root_parent_alternative (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (hroot : W.tiles (identityPose P.p)) :
    CompleteStar P W (identityPose P.p) ∨ CompleteStar P W (W.owner (identityPose P.p)) := by
  classical
  obtain ⟨A, hA, hs⟩ := W.owner_seed P hl _ hroot
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

end RegisteredPrime
