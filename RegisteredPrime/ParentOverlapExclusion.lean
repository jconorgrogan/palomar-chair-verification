module
public import RegisteredPrime.CompleteParentSupport
@[expose] public section
namespace RegisteredPrime

@[simp] theorem identity_inverse_cell {p : Nat} (x : Cell p) : (identityPose p).inv.cell x = x := by
  have h := (identityPose p).cell_inv_cell x
  rwa [identity_cell] at h

/-- A concrete unit cell in both candidate parent supports but in neither centre
forces two distinct full tiles with opposite anchor parities to overlap. -/
theorem standard_stars_not_both (P : Parameters) (W : RegisteredWorld P.p)
    (A : Mask P.p) (hA : Proper A)
    (hOuter : W.tiles (arithmeticChild P (.outer A hA)))
    (hCentre : W.tiles (arithmeticChild P .central))
    (hsOuter : CompleteStar P W (arithmeticChild P (.outer A hA)))
    (hsCentre : CompleteStar P W (arithmeticChild P .central)) : False := by
  obtain ⟨j, hj⟩ := hA
  obtain ⟨k, hkj, _⟩ := third_axis (P.prime.three_le P.odd) j j
  let x : Cell P.p := fun i => if i = j then 0 else
    if i = k then (if A k then 1 else 2) else 2 * bit (A i)
  have hx : DoubledChairCell x := by
    constructor
    · intro i
      by_cases hi : i = j
      · simp [x, hi]
      · by_cases hik : i = k
        · subst i
          cases ha : A k <;> simp [x, hkj, ha]
        · cases ha : A i <;> simp [x, hi, hik, bit, ha]
    · exact ⟨j, by simp [x]⟩
  have hxOuter : DoubledChairCell
      ((centerParent P (arithmeticChild P (.outer A ⟨j, hj⟩))).inv.cell x) := by
    apply centered_outer_parent_contains P A ⟨j, hj⟩ x
    · intro i
      by_cases hi : i = j
      · subst i
        simp [x, bit, hj]
      · by_cases hik : i = k
        · subst i
          cases ha : A k <;> simp [x, hkj, bit, ha]
        · cases ha : A i <;> simp [x, hi, hik, bit, ha]
    · exact ⟨j, hj, by simp [x]⟩
  have hnCentre : ¬ Occupies (arithmeticChild P .central) x := by
    intro h
    have hjx := ((central_image_iff P x).mp h).1 j
    simp [x] at hjx
  have hnOuter : ¬ Occupies (arithmeticChild P (.outer A ⟨j, hj⟩)) x := by
    intro h
    have hkx := ((outer_image_iff P A ⟨j, hj⟩ x).mp h).1 k
    cases ha : A k <;> simp [x, hkj, bit, ha] at hkx
  have hxCentre : DoubledChairCell ((centerParent P (arithmeticChild P .central)).inv.cell x) := by
    rwa [centerParent_standard, identity_inverse_cell]
  obtain ⟨a, ha, hax⟩ := CompleteStar.parent_cover P W _ hCentre hsCentre x hxCentre
  obtain ⟨b, hb, hbx⟩ := CompleteStar.parent_cover P W _ hOuter hsOuter x hxOuter
  rw [centerParent_standard, Pose.identity_comp] at ha hax
  cases a with
  | central => exact hnCentre hax
  | outer B hB =>
    cases b with
    | central =>
      rw [centerParent_central] at hbx
      exact hnOuter hbx
    | outer D hD =>
      have hs := W.nonoverlap _ _ ha hb x hax hbx
      have heven : (arithmeticChild P (.outer B hB)).anchor j % 2 = 0 := by
        rw [child_outer_anchor]
        cases B j <;> decide
      have hodd := centered_outer_child_anchor_odd P A D ⟨j, hj⟩ hD j
      rw [hs.2.2 j] at heven
      omega

/-- Exact full-frame factorization of a sibling hole normal into one common parent. -/
theorem outgoing_seed_factorization (P : Parameters) (q r : Pose P.p)
    (A : Mask P.p) (hA : Proper A) (hs : q.relative r = outgoingSeed P A hA) :
    ∃ t : Pose P.p, t.comp (arithmeticChild P (.outer A hA)) = q ∧ t.comp (arithmeticChild P .central) = r := by
  let Q := arithmeticChild P (.outer A hA)
  refine ⟨q.comp Q.inv, ?_, ?_⟩
  · change (q.comp Q.inv).comp Q = q
    rw [Pose.comp_assoc, Pose.inv_comp, Pose.comp_identity]
  · rw [Pose.comp_assoc]
    change q.comp (outgoingSeed P A hA) = r
    rw [← hs, Pose.comp_relative]

/-- Both actual candidate stars of a tile cannot be complete in a registered E-world. -/
theorem stars_not_both_complete (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (q : Pose P.p) (hq : W.tiles q)
    (hsq : CompleteStar P W q) (hso : CompleteStar P W (W.owner q)) : False := by
  obtain ⟨A, hA, hs⟩ := W.owner_seed P hl q hq
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

end RegisteredPrime
