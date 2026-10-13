module
public import RegisteredPrime.ArithmeticAtlas
public import MeanObstruction.FaceMean
public import RegisteredPrime.WallMasks
public import PrimeFacetClosure.Transport
@[expose] public section

/-!
The finite wall-to-atlas bridge. Its hypotheses are an actual one-wall box
position and equations on every pair of occupied cells sharing that wall.
Neither an atlas contact nor a prescribed contact catalog is a hypothesis.
-/
namespace RegisteredPrime.PrimeFacetClosure
open Uniform

/-- The sign toggle forced by crossing the specified wall axis. -/
def wallToggle {p : Nat} (e : Pose p) (j : Fin p) : Mask p :=
  fun i => xor (e.frame.negative i) (decide (i = j))

/-- The source cell role, pulled back through the actual index permutation. -/
def wallSourceMask {p : Nat} (e : Pose p) (j : Fin p) (A : Mask p) : Mask p :=
  fun k => xor (A (e.frame.inverse k)) (wallToggle e j (e.frame.inverse k))

@[simp] theorem wallSourceMask_at {p : Nat} (e : Pose p) (j : Fin p)
    (A : Mask p) (i : Fin p) :
    wallSourceMask e j A (e.frame.perm i) = xor (A i) (wallToggle e j i) := by
  simp [wallSourceMask, e.frame.left_inverse]

/-- Exact unit-cell facet availability, including the empty endpoints.
The equation says that the source occupied cell is the exterior neighbor of A. -/
theorem wall_shared_cell_iff {p : Nat} (e : Pose p) (j : Fin p) (side : Bool)
    (hbox : boxLower e = wallBox j side) (A B : Mask p) (hside : A j = side) :
    e.cell (fun i => bit (B i)) = exterior A j ↔
      ∀ i, B (e.frame.perm i) = xor (A i) (wallToggle e j i) := by
  constructor
  · intro h i
    have hi := congrFun h i
    have hb := congrFun hbox i
    by_cases hij : i = j
    · subst i
      cases side <;> cases hn : e.frame.negative j <;>
        cases hB : B (e.frame.perm j) <;>
        simp [Pose.cell, RegisteredFrame.linear, RegisteredFrame.sign, exterior,
          boxLower, wallBox, wallToggle, bit, hside, hn, hB] at hi hb ⊢ <;> omega
    · cases hA : A i <;> cases hn : e.frame.negative i <;>
        cases hB : B (e.frame.perm i) <;>
        simp [Pose.cell, RegisteredFrame.linear, RegisteredFrame.sign, exterior,
          boxLower, wallBox, wallToggle, bit, hij, hA, hn, hB] at hi hb ⊢ <;> omega
  · intro h
    funext i
    have hb := congrFun hbox i
    have hi := h i
    by_cases hij : i = j
    · subst i
      cases side <;> cases hn : e.frame.negative j <;>
        cases hB : B (e.frame.perm j) <;>
        simp [Pose.cell, RegisteredFrame.linear, RegisteredFrame.sign, exterior,
          boxLower, wallBox, wallToggle, bit, hside, hn, hB] at hi hb ⊢ <;> omega
    · cases hA : A i <;> cases hn : e.frame.negative i <;>
        cases hB : B (e.frame.perm i) <;>
        simp [Pose.cell, RegisteredFrame.linear, RegisteredFrame.sign, exterior,
          boxLower, wallBox, wallToggle, bit, hij, hA, hn, hB] at hi hb ⊢ <;> omega

theorem wallSourceMask_shared {p : Nat} (e : Pose p) (j : Fin p) (side : Bool)
    (hbox : boxLower e = wallBox j side) (A : Mask p) (hside : A j = side) :
    e.cell (fun i => bit (wallSourceMask e j A i)) = exterior A j :=
  (wall_shared_cell_iff e j side hbox A _ hside).mpr (wallSourceMask_at e j A)

theorem wallSourceMask_proper_iff {p : Nat} (e : Pose p) (j : Fin p) (A : Mask p) :
    Proper (wallSourceMask e j A) ↔ Proper (fun i => xor (A i) (wallToggle e j i)) := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨e.frame.inverse k, hk⟩
  · rintro ⟨i, hi⟩
    exact ⟨e.frame.perm i, by simpa only [wallSourceMask_at] using hi⟩

theorem wallSourceMask_nonempty_iff {p : Nat} (e : Pose p) (j : Fin p) (A : Mask p) :
    NonemptyMask (wallSourceMask e j A) ↔
      NonemptyMask (fun i => xor (A i) (wallToggle e j i)) := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨e.frame.inverse k, hk⟩
  · rintro ⟨i, hi⟩
    exact ⟨e.frame.perm i, by simpa only [wallSourceMask_at] using hi⟩

/-- Explicit full index-frame equations on actual shared outer facets.
The gauged permutation F is supplied by the finite facet-transport graph;
no sign mask, mean equation, recognition or atlas condition is assumed. -/
def WallFacetIndexTransport (P : Parameters) (e : Pose P.p) (j : Fin P.p)
    (side : Bool) (F : RegisteredFrame P.p) : Prop :=
  ∀ (A B : Mask P.p) (hA : Proper A) (hB : Proper B), A j = side →
    e.cell (fun i => bit (B i)) = exterior A j →
    ∀ i, (arithmeticChild P (.outer B hB)).frame.perm
      (e.frame.perm ((arithmeticChild P (.outer A hA)).frame.inverse i)) = F.perm i

/-- Every one-wall placement in dimension at least three has an available
outer facet. Two independent transverse coordinates avoid the two holes. -/
theorem wall_has_shared_roles (P : Parameters) (e : Pose P.p) (j : Fin P.p)
    (side : Bool) (hbox : boxLower e = wallBox j side) :
    ∃ (A B : Mask P.p) (_hA : Proper A) (_hB : Proper B), A j = side ∧
      e.cell (fun i => bit (B i)) = exterior A j := by
  obtain ⟨k, hkj, _⟩ := third_axis (P.prime.three_le P.odd) j j
  obtain ⟨l, hlj, hlk⟩ := third_axis (P.prime.three_le P.odd) j k
  let A : Mask P.p := fun i => if i = j then side else if i = l then wallToggle e j l else false
  have hA : Proper A := ⟨k, by simp [A, hkj, Ne.symm hlk]⟩
  have hside : A j = side := by simp [A]
  have hC : Proper (fun i => xor (A i) (wallToggle e j i)) := by
    refine ⟨l, ?_⟩
    simp [A, hlj]
  have hB := (wallSourceMask_proper_iff e j A).mpr hC
  exact ⟨A, wallSourceMask e j A, hA, hB, hside,
    wallSourceMask_shared e j side hbox A hside⟩

/-- One available gauged affine transport already makes the candidate's
whole index permutation affine. -/
theorem wall_transport_affine (P : Parameters) (e : Pose P.p) (j : Fin P.p)
    (side : Bool) (F : RegisteredFrame P.p) (hbox : boxLower e = wallBox j side)
    (hF : F.AffineIndex) (ht : WallFacetIndexTransport P e j side F) : e.AffineIndex := by
  obtain ⟨A, B, hA, hB, hs, hcell⟩ := wall_has_shared_roles P e j side hbox
  let HA := (arithmeticChild P (.outer A hA)).frame
  let HB := (arithmeticChild P (.outer B hB)).frame
  have hperm : ∀ i, e.frame.perm i = ((HA.comp F).comp HB.inv).perm i := by
    intro i
    have he := ht A B hA hB hs hcell (HA.perm i)
    change HB.perm (e.frame.perm (HA.inverse (HA.perm i))) = F.perm (HA.perm i) at he
    rw [HA.left_inverse] at he
    have hh := congrArg HB.inverse he
    simpa only [HB.left_inverse, RegisteredFrame.comp, RegisteredFrame.inv] using hh
  have ha : ((HA.comp F).comp HB.inv).AffineIndex :=
    RegisteredFrame.AffineIndex.comp P.prime
      (RegisteredFrame.AffineIndex.comp P.prime
        (arithmeticChild_affine_index P (.outer A hA)) hF)
      (RegisteredFrame.AffineIndex.inv P.prime (arithmeticChild_affine_index P (.outer B hB)))
  obtain ⟨a, b, han, hab⟩ := ha
  exact ⟨a, b, han, fun i => by rw [hperm i]; exact hab i⟩

/-- Centering a nonempty outer role identifies its mean intrinsically. -/
theorem wall_transport_mean (P : Parameters) (e : Pose P.p) (j : Fin P.p)
    (side : Bool) (F : RegisteredFrame P.p) (hF0 : F.perm (zeroIndex P) = zeroIndex P)
    (ht : WallFacetIndexTransport P e j side F) (A B : Mask P.p)
    (hA : Proper A) (hB : Proper B) (hnA : NonemptyMask A) (hnB : NonemptyMask B)
    (hs : A j = side) (hc : e.cell (fun i => bit (B i)) = exterior A j) :
    e.frame.perm (maskMeanIndex P A hA hnA) = maskMeanIndex P B hB hnB := by
  have he := ht A B hA hB hs hc (zeroIndex P)
  rw [outer_inverse_zero_mean P A hA hnA, hF0] at he
  have hh := congrArg (arithmeticChild P (.outer B hB)).frame.inverse he
  rw [(arithmeticChild P (.outer B hB)).frame.left_inverse,
    outer_inverse_zero_mean P B hB hnB] at hh
  exact hh

/-- Mean stability is derived on exactly the nonempty shared facets;
empty endpoints are kept separate and no unavailable facet is tested. -/
theorem wall_transport_mean_stable (P : Parameters) (e : Pose P.p) (j : Fin P.p)
    (side : Bool) (F : RegisteredFrame P.p) (hbox : boxLower e = wallBox j side)
    (hF : F.AffineIndex) (hF0 : F.perm (zeroIndex P) = zeroIndex P)
    (ht : WallFacetIndexTransport P e j side F) :
    ∀ A : Mask P.p, NonemptyMask A → Proper A → A j = side →
      NonemptyMask (fun i => xor (A i) (wallToggle e j i)) →
      Proper (fun i => xor (A i) (wallToggle e j i)) →
      zA P.p (extendMask A) = zA P.p (extendMask (fun i => xor (A i) (wallToggle e j i))) := by
  intro A hnA hA hs hnC hC
  let B := wallSourceMask e j A
  have hB : Proper B := (wallSourceMask_proper_iff e j A).mpr hC
  have hnB : NonemptyMask B := (wallSourceMask_nonempty_iff e j A).mpr hnC
  have hmA := wall_transport_mean P e j side F hF0 ht A B hA hB hnA hnB hs
    (wallSourceMask_shared e j side hbox A hs)
  have hmC := affine_mask_mean_index P e.frame
    (wall_transport_affine P e j side F hbox hF ht)
    (fun i => xor (A i) (wallToggle e j i)) B hC hnC hB hnB
    (wallSourceMask_at e j A)
  have he := congrArg e.frame.inverse (hmA.trans hmC.symm)
  rw [e.frame.left_inverse, e.frame.left_inverse] at he
  exact congrArg Fin.val he

/-- The proved mean obstruction rules out every mixed sign toggle. -/
theorem wall_transport_toggle_constant (P : Parameters) (e : Pose P.p) (j : Fin P.p)
    (side : Bool) (F : RegisteredFrame P.p) (hbox : boxLower e = wallBox j side)
    (hF : F.AffineIndex) (hF0 : F.perm (zeroIndex P) = zeroIndex P)
    (ht : WallFacetIndexTransport P e j side F) :
    wallToggle e j = (fun _ => false) ∨ wallToggle e j = (fun _ => true) :=
  registered_mean_obstruction_side P j (wallToggle e j) side
    (wall_transport_mean_stable P e j side F hbox hF hF0 ht)

/-- Thus the actual negative mask is a singleton or its complement. -/
theorem wall_transport_mask (P : Parameters) (e : Pose P.p) (j : Fin P.p)
    (side : Bool) (F : RegisteredFrame P.p) (hbox : boxLower e = wallBox j side)
    (hF : F.AffineIndex) (hF0 : F.perm (zeroIndex P) = zeroIndex P)
    (ht : WallFacetIndexTransport P e j side F) : WallMaskAt e.frame.negative j := by
  rcases wall_transport_toggle_constant P e j side F hbox hF hF0 ht with h | h
  · refine ⟨false, fun i => ?_⟩
    have hi := congrFun h i
    by_cases hij : i = j <;> cases hn : e.frame.negative i <;>
      simp_all [wallToggle]
  · refine ⟨true, fun i => ?_⟩
    have hi := congrFun h i
    by_cases hij : i = j <;> cases hn : e.frame.negative i <;>
      simp_all [wallToggle]

/-- Zero translation can only be the negative singleton wall. This is a
coordinate consequence of the actual box, before the mean obstruction. -/
theorem wall_zero_anchor_data {p : Nat} (e : Pose p) (j : Fin p) (side : Bool)
    (hbox : boxLower e = wallBox j side) (hz : ∀ i, e.anchor i = 0) :
    side = false ∧ wallToggle e j = (fun _ => false) := by
  have hj := congrFun hbox j
  have hs : side = false := by
    cases side <;> cases hn : e.frame.negative j <;>
      simp [boxLower, wallBox, hz, bit, hn] at hj ⊢
  refine ⟨hs, ?_⟩
  funext i
  have hi := congrFun hbox i
  by_cases hij : i = j
  · subst i
    cases hn : e.frame.negative j <;>
      simp [boxLower, wallBox, hz, bit, hs, hn, wallToggle] at hi ⊢
  · cases hn : e.frame.negative i <;>
      simp [boxLower, wallBox, hz, bit, hn, hij, wallToggle] at hi ⊢

/-- The stipulated empty role supplies the zero-origin condition at the
negative singleton endpoint, without ever assigning a mean to the empty set. -/
theorem wall_transport_zero_origin (P : Parameters) (e : Pose P.p) (j : Fin P.p)
    (side : Bool) (F : RegisteredFrame P.p) (hbox : boxLower e = wallBox j side)
    (hF0 : F.perm (zeroIndex P) = zeroIndex P)
    (ht : WallFacetIndexTransport P e j side F) (hz : ∀ i, e.anchor i = 0) :
    e.ZeroOrigin P := by
  obtain ⟨hs, htoggle⟩ := wall_zero_anchor_data e j side hbox hz
  have hcell : e.cell (fun _ => bit false) = exterior (fun _ => false) j := by
    apply (wall_shared_cell_iff e j side hbox (fun _ => false) (fun _ => false) hs.symm).mpr
    intro i
    rw [congrFun htoggle i]
    rfl
  have he := ht (fun _ => false) (fun _ => false) (empty_proper P) (empty_proper P)
    hs.symm hcell (zeroIndex P)
  rw [empty_child_frame, central_inverse_zero, hF0] at he
  have hh := congrArg (arithmeticChild P .central).frame.inverse he
  rw [(arithmeticChild P .central).frame.left_inverse, central_inverse_zero] at hh
  exact hh

/-- Actual wall box coordinates force even translation in every coordinate. -/
theorem wall_anchor_even {p : Nat} (e : Pose p) (j : Fin p) (side : Bool)
    (hbox : boxLower e = wallBox j side) : ∀ i, e.anchor i % 2 = 0 := by
  intro i
  have hi := congrFun hbox i
  by_cases hij : i = j <;> cases side <;> cases hn : e.frame.negative i <;>
    simp_all [boxLower, wallBox, bit] <;> omega

/-- A one-wall box cannot be an incoming hole support. -/
theorem wall_not_incoming {p : Nat} (e : Pose p) (j : Fin p) (side : Bool)
    (hbox : boxLower e = wallBox j side) (A : Mask p) : ¬ IncomingSupport e A := by
  intro hi
  have hj := congrFun (hbox.symm.trans hi.1) j
  cases side <;> cases ha : A j <;> simp [wallBox, bit, ha] at hj

/-- A one-wall box cannot occupy the root's missing cell. -/
theorem wall_not_outgoing {p : Nat} (e : Pose p) (j : Fin p) (side : Bool)
    (hbox : boxLower e = wallBox j side) : ¬ Occupies e (fun _ => 1) := by
  intro ho
  have hj := ((occupies_box_iff e (fun _ => 1)).mp ho).1 j
  rw [congrFun hbox j] at hj
  cases side <;> simp [wallBox] at hj

/-- Concrete wall-to-atlas endpoint. Full finite facet-index equations and
an affine zero-fixing gauged transport imply every clause of the minimal
arithmetic atlas. The sign-mask restriction and mean stability are conclusions. -/
theorem wall_arithmetic_atlas_contact (P : Parameters) (e : Pose P.p) (j : Fin P.p)
    (side : Bool) (F : RegisteredFrame P.p) (hbox : boxLower e = wallBox j side)
    (hF : F.AffineIndex) (hF0 : F.perm (zeroIndex P) = zeroIndex P)
    (ht : WallFacetIndexTransport P e j side F) : ArithmeticAtlasContact P e := by
  have heven := wall_anchor_even e j side hbox
  obtain ⟨color, hmask⟩ := wall_transport_mask P e j side F hbox hF hF0 ht
  refine ⟨⟨⟨false, heven⟩, ?_, ?_, ?_⟩,
    wall_transport_affine P e j side F hbox hF ht,
    wall_transport_zero_origin P e j side F hbox hF0 ht⟩
  · intro _
    exact wall_geometry_of_box_mask e j side color hbox hmask
  · intro A _ hin
    exact False.elim (wall_not_incoming e j side hbox A hin)
  · intro hout
    exact False.elim (wall_not_outgoing e j side hbox hout)

/-- The correctly labelled odd bridge forces the sign equation at an
actual outer facet, in the existing registered row convention. -/
theorem outer_frame_transport_toggle (P : Parameters) (e : Pose P.p)
    (A B : Mask P.p) (hA : Proper A) (hB : Proper B) (j : Fin P.p)
    (F : RegisteredFrame P.p)
    (hframe : (((arithmeticChild P (.outer A hA)).frame.inv.comp e.frame).comp
      (arithmeticChild P (.outer B hB)).frame) =
        bridge F ((arithmeticChild P (.outer A hA)).frame.perm j)) :
    ∀ i, B (e.frame.perm i) = xor (A i) (wallToggle e j i) := by
  intro i
  let H := (arithmeticChild P (.outer A hA)).frame
  have he : H.perm i = H.perm j ↔ i = j := by
    constructor
    · intro h
      have hh := congrArg H.inverse h
      simpa only [H.left_inverse] using hh
    · exact congrArg H.perm
  have hi := congrArg (fun G : RegisteredFrame P.p => G.negative (H.perm i)) hframe
  change xor (xor (H.negative (H.inverse (H.perm i)))
    (e.frame.negative (H.inverse (H.perm i))))
      ((arithmeticChild P (.outer B hB)).frame.negative
        (e.frame.perm (H.inverse (H.perm i)))) = decide (H.perm i = H.perm j) at hi
  simp only [H.left_inverse, he] at hi
  simp only [H, child_outer_negative] at hi
  by_cases hij : i = j <;> cases ha : A i <;> cases hn : e.frame.negative i <;>
    cases hb : B (e.frame.perm i) <;> simp_all [wallToggle]

/-- A single genuine outer/outer facet with its correctly labelled odd
transport already forces the one-axis wall displacement. In particular the
box position is not an extra closure certificate. -/
theorem outer_frame_transport_wall_box (P : Parameters) (e : Pose P.p)
    (A B : Mask P.p) (hA : Proper A) (hB : Proper B) (j : Fin P.p)
    (F : RegisteredFrame P.p)
    (hcell : e.cell (fun i => bit (B i)) = exterior A j)
    (hframe : (((arithmeticChild P (.outer A hA)).frame.inv.comp e.frame).comp
      (arithmeticChild P (.outer B hB)).frame) =
        bridge F ((arithmeticChild P (.outer A hA)).frame.perm j)) :
    boxLower e = wallBox j (A j) := by
  have ht := outer_frame_transport_toggle P e A B hA hB j F hframe
  funext i
  have hi := congrFun hcell i
  have hm := ht i
  by_cases hij : i = j
  · subst i
    cases ha : A j <;> cases hn : e.frame.negative j <;> cases hb : B (e.frame.perm j) <;>
      simp [Pose.cell, RegisteredFrame.linear, RegisteredFrame.sign, exterior,
        boxLower, wallBox, wallToggle, bit, ha, hn, hb] at hi hm ⊢ <;> omega
  · cases ha : A i <;> cases hn : e.frame.negative i <;> cases hb : B (e.frame.perm i) <;>
      simp [Pose.cell, RegisteredFrame.linear, RegisteredFrame.sign, exterior,
        boxLower, wallBox, wallToggle, bit, hij, ha, hn, hb] at hi hm ⊢ <;> omega

/-- Adapter from full gauged frame equalities produced by the finite
transport graph. The bridge axis may vary over the shared facets. -/
theorem wall_index_transport_of_frames (P : Parameters) (e : Pose P.p)
    (j : Fin P.p) (side : Bool) (F : RegisteredFrame P.p)
    (hframes : ∀ (A B : Mask P.p) (hA : Proper A) (hB : Proper B), A j = side →
      e.cell (fun i => bit (B i)) = exterior A j →
      ∃ k : Fin P.p,
        (((arithmeticChild P (.outer A hA)).frame.inv.comp e.frame).comp
          (arithmeticChild P (.outer B hB)).frame) = bridge F k) :
    WallFacetIndexTransport P e j side F := by
  intro A B hA hB hs hc i
  obtain ⟨k, hk⟩ := hframes A B hA hB hs hc
  exact congrArg (fun H : RegisteredFrame P.p => H.perm i) hk

/-- Full-frame form of the wall-to-atlas implication. This is the direct
consumer for odd facet-graph transport; no E/CL catalog is needed. -/
theorem wall_arithmetic_atlas_of_frame_transport (P : Parameters) (e : Pose P.p)
    (j : Fin P.p) (side : Bool) (F : RegisteredFrame P.p)
    (hbox : boxLower e = wallBox j side) (hF : F.AffineIndex)
    (hF0 : F.perm (zeroIndex P) = zeroIndex P)
    (hframes : ∀ (A B : Mask P.p) (hA : Proper A) (hB : Proper B), A j = side →
      e.cell (fun i => bit (B i)) = exterior A j →
      ∃ k : Fin P.p,
        (((arithmeticChild P (.outer A hA)).frame.inv.comp e.frame).comp
          (arithmeticChild P (.outer B hB)).frame) = bridge F k) :
    ArithmeticAtlasContact P e :=
  wall_arithmetic_atlas_contact P e j side F hbox hF hF0
    (wall_index_transport_of_frames P e j side F hframes)

/-- Box-free endpoint: a witnessed outer facet and the full-index equations
on every actual shared facet imply arithmetic atlas membership. -/
theorem outer_facet_arithmetic_atlas_contact (P : Parameters) (e : Pose P.p)
    (A B : Mask P.p) (hA : Proper A) (hB : Proper B) (j : Fin P.p)
    (F : RegisteredFrame P.p) (hF : F.AffineIndex)
    (hF0 : F.perm (zeroIndex P) = zeroIndex P)
    (hcell : e.cell (fun i => bit (B i)) = exterior A j)
    (hframe : (((arithmeticChild P (.outer A hA)).frame.inv.comp e.frame).comp
      (arithmeticChild P (.outer B hB)).frame) =
        bridge F ((arithmeticChild P (.outer A hA)).frame.perm j))
    (ht : WallFacetIndexTransport P e j (A j) F) : ArithmeticAtlasContact P e :=
  wall_arithmetic_atlas_contact P e j (A j) F
    (outer_frame_transport_wall_box P e A B hA hB j F hcell hframe) hF hF0 ht

/-- Complete outer-facet frame matching, stated solely on finite roles and
actual shared unit-cell equations. This contains no atlas or closure clause. -/
def OuterFacetFrameTransport (P : Parameters) (e : Pose P.p)
    (F : RegisteredFrame P.p) : Prop :=
  ∀ (A B : Mask P.p) (hA : Proper A) (hB : Proper B) (j : Fin P.p),
    e.cell (fun i => bit (B i)) = exterior A j →
    (((arithmeticChild P (.outer A hA)).frame.inv.comp e.frame).comp
      (arithmeticChild P (.outer B hB)).frame) =
        bridge F ((arithmeticChild P (.outer A hA)).frame.perm j)

/-- The complete catalog-free outer/outer bridge. The sole geometric witness
is one actual shared outer facet; all wall geometry and atlas conditions are
derived from full-profile frame matching and the proved mean obstruction. -/
theorem outer_facets_arithmetic_atlas_contact (P : Parameters) (e : Pose P.p)
    (F : RegisteredFrame P.p) (hF : F.AffineIndex)
    (hF0 : F.perm (zeroIndex P) = zeroIndex P)
    (ht : OuterFacetFrameTransport P e F)
    (hwitness : ∃ (A B : Mask P.p) (_hA : Proper A) (_hB : Proper B) (j : Fin P.p),
      e.cell (fun i => bit (B i)) = exterior A j) : ArithmeticAtlasContact P e := by
  obtain ⟨A, B, hA, hB, j, hc⟩ := hwitness
  apply outer_facet_arithmetic_atlas_contact P e A B hA hB j F hF hF0 hc
    (ht A B hA hB j hc)
  apply wall_index_transport_of_frames
  intro C D hC hD _ hCD
  exact ⟨(arithmeticChild P (.outer C hC)).frame.perm j, ht C D hC hD j hCD⟩

#print axioms outer_facets_arithmetic_atlas_contact
#print axioms outer_frame_transport_wall_box
#print axioms outer_facet_arithmetic_atlas_contact
#print axioms wall_shared_cell_iff
#print axioms wall_transport_mean_stable
#print axioms wall_transport_mask
#print axioms wall_transport_zero_origin
#print axioms wall_arithmetic_atlas_contact
#print axioms wall_arithmetic_atlas_of_frame_transport
end RegisteredPrime.PrimeFacetClosure
