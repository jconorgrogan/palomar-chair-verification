module
public import closure_analysis.ZeroOriginBinding
public import MeanObstruction.FaceMean
public import RegisteredPrime.WallMasks
@[expose] public section
namespace RegisteredPrime
open Uniform

/-- The sign discrepancy left after crossing the chosen coarse face. -/
def wallDiscrepancy {p : Nat} (e : Pose p) (j : Fin p) : Mask p :=
  fun i => xor (e.frame.negative i) (decide (i = j))

/-- The matching outer corner lies one actual cell step across the coarse
wall, for either face orientation. -/
theorem wall_matching_cells_adjacent (P : Parameters) (e : Pose P.p)
    (j : Fin P.p) (side : Bool) (hbox : boxLower e = wallBox j side)
    (A B : Mask P.p) (hAj : A j = side)
    (hAB : ∀ i, B (e.frame.perm i) = xor (A i) (wallDiscrepancy e j i)) :
    Adjacent (fun i => bit (A i)) (e.cell (fun i => bit (B i))) := by
  have hcoord : ∀ i, e.cell (fun k => bit (B k)) i =
      bit (A i) + if i = j then (if side then 1 else -1) else 0 := by
    intro i
    have hb := congrFun hbox i
    simp only [Pose.cell, RegisteredFrame.linear, hAB, wallDiscrepancy]
    by_cases hij : i = j
    · subst i
      rw [hAj]
      cases side <;> rcases Bool.eq_false_or_eq_true (e.frame.negative j) with hd | hd <;>
        simp [boxLower, wallBox, bit, RegisteredFrame.sign, hd] at hb ⊢ <;> omega
    · cases ha : A i <;> rcases Bool.eq_false_or_eq_true (e.frame.negative i) with hd | hd <;>
        simp [boxLower, wallBox, bit, RegisteredFrame.sign, hd, hij] at hb ⊢ <;> omega
  refine ⟨j, ?_, ?_⟩
  · rw [hcoord j]
    cases side <;> simp <;> omega
  · intro i hij
    rw [hcoord i]
    simp [hij]

/-- The actual matching boundary outer children have equal full anchors. -/
theorem wall_matching_outer_anchors (P : Parameters) (e : Pose P.p)
    (j : Fin P.p) (side : Bool) (hbox : boxLower e = wallBox j side)
    (A B : Mask P.p) (hA : Proper A) (hB : Proper B) (hAj : A j = side)
    (hAB : ∀ i, B (e.frame.perm i) = xor (A i) (wallDiscrepancy e j i)) :
    (arithmeticChild P (.outer A hA)).anchor = (refine P e (.outer B hB)).anchor := by
  funext i
  have hb := congrFun hbox i
  rw [child_outer_anchor, refine_outer_anchor, hAB]
  simp only [wallDiscrepancy]
  by_cases hij : i = j
  · subst i
    rw [hAj]
    cases side <;> rcases Bool.eq_false_or_eq_true (e.frame.negative j) with hd | hd <;>
      simp [boxLower, wallBox, bit, RegisteredFrame.sign, hd] at hb ⊢ <;> omega
  · cases ha : A i <;> rcases Bool.eq_false_or_eq_true (e.frame.negative i) with hd | hd <;>
      simp [boxLower, wallBox, bit, RegisteredFrame.sign, hd, hij] at hb ⊢ <;> omega

/-- All eligible face masks produce genuine zero-anchor fine contacts. The
arithmetic mean obstruction therefore forces exactly the two wall sign masks.
There is no symbolic catalog or coarse recognition premise. -/
theorem coarse_wall_mask_of_zero_tests (P : Parameters) (e : Pose P.p)
    (j : Fin P.p) (side : Bool) (hbox : boxLower e = wallBox j side)
    (haff : e.AffineIndex)
    (hzero : ∀ a b : Role P.p,
      FaceContact (arithmeticChild P a) (refine P e b) →
      (∀ i, ((arithmeticChild P a).relative (refine P e b)).anchor i = 0) →
      ((arithmeticChild P a).relative (refine P e b)).ZeroOrigin P) :
    WallMaskAt e.frame.negative j := by
  let L := wallDiscrepancy e j
  have hL : L = (fun _ => false) ∨ L = (fun _ => true) := by
    apply registered_mean_obstruction_side P j L side
    intro A hnA hA hAj hnC hC
    let C : Mask P.p := fun i => xor (A i) (L i)
    let B : Mask P.p := fun i => C (e.frame.inverse i)
    have hBC : ∀ i, B (e.frame.perm i) = C i := by
      intro i
      simp only [B, e.frame.left_inverse]
    have hB : Proper B := by
      obtain ⟨i, hi⟩ := hC
      exact ⟨e.frame.perm i, (hBC i).trans hi⟩
    have hAB : ∀ i, B (e.frame.perm i) = xor (A i) (wallDiscrepancy e j i) := hBC
    have hc := refined_outer_contact_of_adjacent_cells P (identityPose P.p) e A B hA hB
      (by simpa only [identity_cell] using wall_matching_cells_adjacent P e j side hbox A B hAj hAB)
    rw [(identity_refine_same P (.outer A hA)).eq] at hc
    have hanchor := wall_matching_outer_anchors P e j side hbox A B hA hB hAj hAB
    have hz := hzero (.outer A hA) (.outer B hB) hc
      ((relative_anchor_zero_iff _ _).mpr hanchor)
    exact outer_zero_origin_forces_mean_eq P e haff A B C hA hnA hB hC hnC hBC hz
  rcases hL with hL | hL
  · refine ⟨false, fun i => ?_⟩
    have hi := congrFun hL i
    change xor (e.frame.negative i) (decide (i = j)) = false at hi
    by_cases hij : i = j <;> simpa [hij] using hi
  · refine ⟨true, fun i => ?_⟩
    have hi := congrFun hL i
    change xor (e.frame.negative i) (decide (i = j)) = true at hi
    by_cases hij : i = j <;> simpa [hij] using hi

/-- Coarse wall geometry follows from actual fine zero-origin tests and an
affine coarse index permutation, uniformly for every parameter and side. -/
theorem coarse_wall_geometry_of_zero_tests (P : Parameters) (e : Pose P.p)
    (j : Fin P.p) (side : Bool) (hbox : boxLower e = wallBox j side)
    (haff : e.AffineIndex)
    (hzero : ∀ a b : Role P.p,
      FaceContact (arithmeticChild P a) (refine P e b) →
      (∀ i, ((arithmeticChild P a).relative (refine P e b)).anchor i = 0) →
      ((arithmeticChild P a).relative (refine P e b)).ZeroOrigin P) :
    WallGeometry e := by
  obtain ⟨color, hmask⟩ := coarse_wall_mask_of_zero_tests P e j side hbox haff hzero
  exact wall_geometry_of_box_mask e j side color hbox hmask

/-- A canonical wall at zero anchor necessarily has the negative singleton
sign mask. This is just its actual box lower corner equation. -/
theorem zero_anchor_wall_singleton (P : Parameters) (e : Pose P.p)
    (j : Fin P.p) (side : Bool) (hbox : boxLower e = wallBox j side)
    (hz : ∀ i, e.anchor i = 0) :
    side = false ∧ ∀ i, e.frame.negative i = decide (i = j) := by
  have hj := congrFun hbox j
  have hs : side = false := by
    cases side <;> rcases Bool.eq_false_or_eq_true (e.frame.negative j) with hd | hd <;>
      simp [boxLower, wallBox, hz, bit, hd] at hj ⊢
  refine ⟨hs, fun i => ?_⟩
  have hi := congrFun hbox i
  rw [hs] at hi
  by_cases hij : i = j
  · subst i
    rcases Bool.eq_false_or_eq_true (e.frame.negative j) with hd | hd <;>
      simp [boxLower, wallBox, hz, bit, hd] at hi ⊢
  · rcases Bool.eq_false_or_eq_true (e.frame.negative i) with hd | hd <;>
      simp [boxLower, wallBox, hz, bit, hd, hij] at hi ⊢

/-- The empty--empty actual fine contact reflects the fixed-origin condition
back to a zero-anchor coarse wall. No mean is assigned to an empty mask. -/
theorem coarse_zero_origin_wall_of_zero_tests (P : Parameters) (e : Pose P.p)
    (j : Fin P.p) (side : Bool) (hbox : boxLower e = wallBox j side)
    (hzero : ∀ a b : Role P.p,
      FaceContact (arithmeticChild P a) (refine P e b) →
      (∀ i, ((arithmeticChild P a).relative (refine P e b)).anchor i = 0) →
      ((arithmeticChild P a).relative (refine P e b)).ZeroOrigin P)
    (hz : ∀ i, e.anchor i = 0) : e.ZeroOrigin P := by
  obtain ⟨hs, hmask⟩ := zero_anchor_wall_singleton P e j side hbox hz
  have hAB : ∀ i, (fun _ => false) (e.frame.perm i) =
      xor ((fun _ => false) i) (wallDiscrepancy e j i) := by
    intro i
    simp [wallDiscrepancy, hmask i]
  have hAj : (fun _ : Fin P.p => false) j = side := hs.symm
  have hc := refined_outer_contact_of_adjacent_cells P (identityPose P.p) e
    (fun _ => false) (fun _ => false) (empty_proper P) (empty_proper P)
    (by simpa only [identity_cell] using (wall_matching_cells_adjacent P e j side hbox
      (fun _ => false) (fun _ => false) hAj hAB))
  rw [(identity_refine_same P (.outer (fun _ => false) (empty_proper P))).eq] at hc
  have hanchor := wall_matching_outer_anchors P e j side hbox
    (fun _ => false) (fun _ => false) (empty_proper P) (empty_proper P) hAj hAB
  exact (empty_relative_zero_origin_iff P e).mp
    (hzero (.outer (fun _ => false) (empty_proper P))
      (.outer (fun _ => false) (empty_proper P)) hc
      ((relative_anchor_zero_iff _ _).mpr hanchor))

/-- Both wall obligations preserved by the explicit fine tests: the full
allowed wall geometry and, when the coarse anchor is zero, index zero. -/
theorem coarse_wall_preservation (P : Parameters) (e : Pose P.p)
    (j : Fin P.p) (side : Bool) (hbox : boxLower e = wallBox j side)
    (haff : e.AffineIndex)
    (hzero : ∀ a b : Role P.p,
      FaceContact (arithmeticChild P a) (refine P e b) →
      (∀ i, ((arithmeticChild P a).relative (refine P e b)).anchor i = 0) →
      ((arithmeticChild P a).relative (refine P e b)).ZeroOrigin P) :
    WallGeometry e ∧ ((∀ i, e.anchor i = 0) → e.ZeroOrigin P) :=
  ⟨coarse_wall_geometry_of_zero_tests P e j side hbox haff hzero,
    coarse_zero_origin_wall_of_zero_tests P e j side hbox hzero⟩

end RegisteredPrime
