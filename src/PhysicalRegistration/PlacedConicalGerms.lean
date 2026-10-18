module

public import PhysicalRegistration.GenericIncidentKeys
public import PhysicalRegistration.PhysicalTilingGerms
public import PhysicalRegistration.CreaseSectors

@[expose] public section

/-! Actual local body germs in centered world directions, under unrestricted
ambient isometric placements. All cones below are conclusions, not tiling data. -/
namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace Topology
open Set
noncomputable section

/-- Exact agreement of an actual set with a centered cone on a positive ball. -/
def HasCenteredGerm {m : ℕ} (S : Set (Space m)) (x : Space m)
    (C : Set (Space m)) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ z, ‖z‖ < r → (x + z ∈ S ↔ z ∈ C)

/-- The two closed signs of every listed normal determine membership. -/
def SignDetermined {m : ℕ} (N : Finset (Space m)) (C : Set (Space m)) : Prop :=
  ∀ z w, (∀ n ∈ N, (⟪n, z⟫_ℝ ≤ 0 ↔ ⟪n, w⟫_ℝ ≤ 0) ∧
    (0 ≤ ⟪n, z⟫_ℝ ↔ 0 ≤ ⟪n, w⟫_ℝ)) → (z ∈ C ↔ w ∈ C)

/-- Sign-defined sets are homogeneous under every strictly positive scaling. -/
theorem SignDetermined.homogeneous {m : ℕ} {N : Finset (Space m)}
    {C : Set (Space m)} (h : SignDetermined N C) (t : ℝ) (ht : 0 < t)
    (z : Space m) : t • z ∈ C ↔ z ∈ C := by
  apply h
  intro n hn
  simp only [real_inner_smul_right]
  constructor <;> constructor <;> intro hsign <;> nlinarith

/-- Isometric transport identifies inner products with actual centered world
vectors, with no restriction on rotation, reflection, or translation. -/
theorem placedNormal_inner_sub {m : ℕ} (f : Space m ≃ᵢ Space m)
    (n y x : Space m) :
    ⟪placedNormal f n, y - x⟫_ℝ = ⟪n, f.symm y - f.symm x⟫_ℝ := by
  have hv := f.toRealAffineIsometryEquiv.map_vsub (f.symm y) (f.symm x)
  change f.toRealAffineIsometryEquiv.linearIsometryEquiv
    (f.symm y - f.symm x) = f (f.symm y) - f (f.symm x) at hv
  rw [f.apply_symm_apply, f.apply_symm_apply] at hv
  rw [← hv]
  exact f.toRealAffineIsometryEquiv.linearIsometryEquiv.inner_map_map _ _

theorem placed_centered_halfspace_iff {m : ℕ} (f : Space m ≃ᵢ Space m)
    (x n c : Space m) (b : ℝ) (hx : ⟪n, f.symm x - c⟫_ℝ = b)
    (z : Space m) :
    ⟪n, f.symm (x + z) - c⟫_ℝ ≤ b ↔ ⟪placedNormal f n, z⟫_ℝ ≤ 0 := by
  have h := placedNormal_inner_sub f n (x + z) x
  rw [add_sub_cancel_left] at h
  have hs : f.symm (x + z) - c =
      (f.symm (x + z) - f.symm x) + (f.symm x - c) := by abel
  rw [hs, inner_add_right, hx, ← h]
  exact add_le_iff_nonpos_left

/-- Transport any already-proved native open membership formula and then
extract a genuine radius in the ambient world metric. -/
theorem placed_hasCenteredGerm_of_local_formula
    {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x : Space m) (C : Set (Space m))
    (U : Set (Space m)) (hU : IsOpen U) (hxU : f.symm x ∈ U)
    (heq : ∀ z, f.symm (x + z) ∈ U →
      (f.symm (x + z) ∈ body a ↔ z ∈ C)) :
    HasCenteredGerm (placedBody a f) x C := by
  have hV : IsOpen (f '' U) := f.toHomeomorph.isOpenMap U hU
  have hxV : x ∈ f '' U := ⟨f.symm x, hxU, f.apply_symm_apply x⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV x hxV
  refine ⟨r, hr, fun z hz => ?_⟩
  have hxz : x + z ∈ f '' U := hball (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  have hpre : f.symm (x + z) ∈ U := by
    rcases hxz with ⟨y, hy, hxy⟩
    simpa [← hxy] using hy
  have hm : x + z ∈ placedBody a f ↔ f.symm (x + z) ∈ body a := by
    change x + z ∈ f '' body a ↔ _
    constructor
    · rintro ⟨y, hy, hxy⟩
      simpa [← hxy] using hy
    · intro hy
      exact ⟨f.symm (x + z), hy, f.apply_symm_apply _⟩
  exact hm.trans (heq z hpre)

/-- The actual halfspace germ of every placed strict key side, in centered
world directions and with the computed transported normal. -/
theorem placed_strictSide_hasCenteredGerm
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x : Space m) (u : Site m) (s : Side m)
    (hx : f.symm x ∈ keyGraph a u)
    (hs : f.symm x ∈ strictBranchRegion J u s) :
    HasCenteredGerm (placedBody a f) x
      {z | ⟪placedNormal f (sideNormal a u s), z⟫_ℝ ≤ 0} := by
  obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_side_halfspace hm a u s (f.symm x) hx hs
  have hplane := sideFace_plane a u s (f.symm x)
    (show f.symm x ∈ sideFace a u s from ⟨hx, strictBranchRegion_subset J u s hs⟩)
  apply placed_hasCenteredGerm_of_local_formula a f x _ U hU hxU
  intro z hz
  exact (heq _ hz).trans (placed_centered_halfspace_iff f x _ _ _ hplane z)

/-- Two-normal Boolean cone, with the sign selecting union or intersection. -/
def twoHalfspaceCone {m : ℕ} (p q : Space m) (union : Bool) : Set (Space m) :=
  {z | if union then ⟪p, z⟫_ℝ ≤ 0 ∨ ⟪q, z⟫_ℝ ≤ 0
    else ⟪p, z⟫_ℝ ≤ 0 ∧ ⟪q, z⟫_ℝ ≤ 0}

theorem twoHalfspaceCone_signDetermined {m : ℕ} (p q : Space m) (b : Bool) :
    SignDetermined {p, q} (twoHalfspaceCone p q b) := by
  intro z w h
  have hp := (h p (by simp)).1
  have hq := (h q (by simp)).1
  cases b <;> simp only [twoHalfspaceCone, Bool.false_eq_true, ite_false,
    ite_true, mem_ofPred_eq] <;> tauto

/-- A generic base crease is an actual union/intersection of its carrier and
side halfspaces after any ambient placement. -/
theorem placed_genericBase_hasCenteredGerm
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x : Space m) (u : Site m) (s : Side m)
    (hx : f.symm x ∈ genericBaseCrease a u s) :
    HasCenteredGerm (placedBody a f) x
      (twoHalfspaceCone (placedNormal f (outward u.1))
        (placedNormal f (sideNormal a u s)) (decide (0 < (a.value u : ℝ)))) := by
  have hkey : f.symm x ∈ keyGraph a u := hx.1.1.1
  have hzero : normalCoord u (f.symm x) = 0 := hx.1.2
  have hside := sideFace_plane a u s (f.symm x) hx.1.1
  have hcarrier (z : Space m) : normalCoord u (f.symm (x + z)) ≤ 0 ↔
      ⟪placedNormal f (outward u.1), z⟫_ℝ ≤ 0 :=
    placed_centered_halfspace_iff f x (outward u.1) (siteCenter u) 0 hzero z
  have hside' (z : Space m) := placed_centered_halfspace_iff f x _ _ _ hside z
  by_cases ha : 0 < (a.value u : ℝ)
  · obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_base_sector_pos hm a u s
      (f.symm x) hkey hx.2.1 hx.2.2 ha
    apply placed_hasCenteredGerm_of_local_formula a f x _ U hU hxU
    intro z hz
    simpa only [twoHalfspaceCone, ha, decide_true, ite_true, mem_ofPred_eq,
      hcarrier z, hside' z] using heq _ hz
  · have hne : (a.value u : ℝ) ≠ 0 := by exact_mod_cast a.nonzero u
    have hneg : (a.value u : ℝ) < 0 := lt_of_le_of_ne (le_of_not_gt ha) hne
    obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_base_sector_neg hm a u s
      (f.symm x) hkey hx.2.1 hx.2.2 hneg
    apply placed_hasCenteredGerm_of_local_formula a f x _ U hU hxU
    intro z hz
    simpa only [twoHalfspaceCone, ha, decide_false, Bool.false_eq_true, ite_false,
      mem_ofPred_eq, hcarrier z, hside' z] using heq _ hz

/-- The corresponding actual world cone at a generic side-side crease. -/
theorem placed_genericSide_hasCenteredGerm
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x : Space m) (u : Site m) (s t : Side m)
    (hx : f.symm x ∈ genericSideCrease a u s t) :
    HasCenteredGerm (placedBody a f) x
      (twoHalfspaceCone (placedNormal f (sideNormal a u s))
        (placedNormal f (sideNormal a u t)) (decide ((a.value u : ℝ) < 0))) := by
  have hkey : f.symm x ∈ keyGraph a u := hx.1.1.1
  have hs := sideFace_plane a u s (f.symm x) hx.1.1
  have ht := sideFace_plane a u t (f.symm x) hx.1.2
  have hs' (z : Space m) := placed_centered_halfspace_iff f x _ _ _ hs z
  have ht' (z : Space m) := placed_centered_halfspace_iff f x _ _ _ ht z
  by_cases ha : (a.value u : ℝ) < 0
  · obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_side_sector_neg hm a u s t
      (f.symm x) hkey hx.2.1 hx.2.2.1 hx.2.2.2 ha
    apply placed_hasCenteredGerm_of_local_formula a f x _ U hU hxU
    intro z hz
    simpa only [twoHalfspaceCone, ha, decide_true, ite_true, mem_ofPred_eq,
      hs' z, ht' z] using heq _ hz
  · have hne : (a.value u : ℝ) ≠ 0 := by exact_mod_cast a.nonzero u
    have hpos : 0 < (a.value u : ℝ) := lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm hne)
    obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_side_sector_pos hm a u s t
      (f.symm x) hkey hx.2.1 hx.2.2.1 hx.2.2.2 hpos
    apply placed_hasCenteredGerm_of_local_formula a f x _ U hU hxU
    intro z hz
    simpa only [twoHalfspaceCone, ha, decide_false, Bool.false_eq_true, ite_false,
      mem_ofPred_eq, hs' z, ht' z] using heq _ hz

/-- Literal world-coordinate normals of the untouched carrier. -/
def placedCoordinateNormal {m : ℕ} (f : Space m ≃ᵢ Space m)
    (i : Fin (m + 1)) : Space m :=
  placedNormal f (EuclideanSpace.single i 1)

/-- Every transported coordinate normal is a unit vector. -/
theorem placedCoordinateNormal_unit {m : ℕ} (f : Space m ≃ᵢ Space m)
    (i : Fin (m + 1)) : ‖placedCoordinateNormal f i‖ = 1 := by
  simp [placedCoordinateNormal, placedNormal]

/-- Distinct active coordinate signs use orthogonal world normals. -/
theorem placedCoordinateNormal_orthogonal {m : ℕ} (f : Space m ≃ᵢ Space m)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    ⟪placedCoordinateNormal f i, placedCoordinateNormal f j⟫_ℝ = 0 := by
  change ⟪f.toRealAffineIsometryEquiv.linearIsometryEquiv _,
    f.toRealAffineIsometryEquiv.linearIsometryEquiv _⟫_ℝ = 0
  rw [f.toRealAffineIsometryEquiv.linearIsometryEquiv.inner_map_map]
  simp [EuclideanSpace.inner_single_left, hij]

/-- The ordinary carrier cone, using exactly the active integer coordinate
planes and the literal Boolean formula for the chair carrier. -/
def placedCarrierCone {m : ℕ} (f : Space m ≃ᵢ Space m) (x : Space m) :
    Set (Space m) :=
  {z | (∀ i, ((f.symm x) i = 0 → 0 ≤ ⟪placedCoordinateNormal f i, z⟫_ℝ) ∧
      ((f.symm x) i = 2 → ⟪placedCoordinateNormal f i, z⟫_ℝ ≤ 0)) ∧
    ∃ i, (f.symm x) i < 1 ∨
      ((f.symm x) i = 1 ∧ ⟪placedCoordinateNormal f i, z⟫_ℝ ≤ 0)}

def placedActiveCarrierNormals {m : ℕ} (f : Space m ≃ᵢ Space m)
    (x : Space m) : Finset (Space m) :=
  (activeCarrierAxes (f.symm x)).image (placedCoordinateNormal f)

theorem placedCoordinateNormal_inner {m : ℕ} (f : Space m ≃ᵢ Space m)
    (x z : Space m) (i : Fin (m + 1)) :
    ⟪placedCoordinateNormal f i, z⟫_ℝ =
      (f.symm (x + z)) i - (f.symm x) i := by
  have h := placedNormal_inner_sub f (EuclideanSpace.single i 1) (x + z) x
  simpa [placedCoordinateNormal, EuclideanSpace.inner_single_left] using h

theorem placedCarrierCone_signDetermined {m : ℕ}
    (f : Space m ≃ᵢ Space m) (x : Space m) :
    SignDetermined (placedActiveCarrierNormals f x) (placedCarrierCone f x) := by
  intro z w h
  have hi (i : Fin (m + 1))
      (hi : (f.symm x) i = 0 ∨ (f.symm x) i = 1 ∨ (f.symm x) i = 2) :=
    h (placedCoordinateNormal f i) (Finset.mem_image.mpr
      ⟨i, by simpa [activeCarrierAxes] using hi, rfl⟩)
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor <;> rintro ⟨hzw, ⟨i, hi'⟩⟩
  · refine ⟨fun j => ⟨fun hj => ((hi j (Or.inl hj)).2).mp ((hzw j).1 hj),
      fun hj => ((hi j (Or.inr (Or.inr hj))).1).mp ((hzw j).2 hj)⟩, i, ?_⟩
    rcases hi' with hi' | ⟨he, hs⟩
    · exact Or.inl hi'
    · exact Or.inr ⟨he, ((hi i (Or.inr (Or.inl he))).1).mp hs⟩
  · refine ⟨fun j => ⟨fun hj => ((hi j (Or.inl hj)).2).mpr ((hzw j).1 hj),
      fun hj => ((hi j (Or.inr (Or.inr hj))).1).mpr ((hzw j).2 hj)⟩, i, ?_⟩
    rcases hi' with hi' | ⟨he, hs⟩
    · exact Or.inl hi'
    · exact Or.inr ⟨he, ((hi i (Or.inr (Or.inl he))).1).mpr hs⟩

/-- The untouched ordinary boundary has its explicit homogeneous Boolean
carrier cone as an actual membership germ. -/
theorem placed_ordinary_hasCenteredGerm
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x : Space m)
    (hx : f.symm x ∈ frontier (body a))
    (hkey : ∀ u, f.symm x ∉ keyGraph a u) :
    HasCenteredGerm (placedBody a f) x (placedCarrierCone f x) := by
  obtain ⟨_, U, hU, hxU, _, hbody⟩ :=
    frontier_body_outside_keyGraphs hm a (f.symm x) hx hkey
  have hcarrier : f.symm x ∈ carrier m :=
    (hbody _ hxU).mp ((body_isClosed a).frontier_subset hx)
  obtain ⟨V, hV, hxV, hcoord⟩ := carrier_local_coordinate_germ (f.symm x) hcarrier
  apply placed_hasCenteredGerm_of_local_formula a f x _ (U ∩ V)
    (hU.inter hV) ⟨hxU, hxV⟩
  intro z hz
  rw [hbody _ hz.1, hcoord _ hz.2]
  have h0 (i : Fin (m + 1)) (hi : (f.symm x) i = 0) :
      0 ≤ (f.symm (x + z)) i ↔ 0 ≤ ⟪placedCoordinateNormal f i, z⟫_ℝ := by
    rw [placedCoordinateNormal_inner, hi, sub_zero]
  have h1 (i : Fin (m + 1)) (hi : (f.symm x) i = 1) :
      (f.symm (x + z)) i ≤ 1 ↔ ⟪placedCoordinateNormal f i, z⟫_ℝ ≤ 0 := by
    rw [placedCoordinateNormal_inner, hi, sub_nonpos]
  have h2 (i : Fin (m + 1)) (hi : (f.symm x) i = 2) :
      (f.symm (x + z)) i ≤ 2 ↔ ⟪placedCoordinateNormal f i, z⟫_ℝ ≤ 0 := by
    rw [placedCoordinateNormal_inner, hi, sub_nonpos]
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor <;> rintro ⟨hh, ⟨i, hi⟩⟩
  · refine ⟨fun j => ⟨fun hj => (h0 j hj).mp ((hh j).1 hj),
      fun hj => (h2 j hj).mp ((hh j).2 hj)⟩, i, ?_⟩
    rcases hi with hi | ⟨he, hi⟩
    · exact Or.inl hi
    · exact Or.inr ⟨he, (h1 i he).mp hi⟩
  · refine ⟨fun j => ⟨fun hj => (h0 j hj).mpr ((hh j).1 hj),
      fun hj => (h2 j hj).mpr ((hh j).2 hj)⟩, i, ?_⟩
    rcases hi with hi | ⟨he, hi⟩
    · exact Or.inl hi
    · exact Or.inr ⟨he, (h1 i he).mpr hi⟩

/-- The ordinary cone's actual active normals are in the proved world span,
and there are at most two of them. -/
theorem placedActiveCarrierNormals_span_card
    {m J : ℕ} (a : Coefficients m J) (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hplanes : ∀ b : BoundaryPlaneIndex m, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    (placedActiveCarrierNormals f x).card ≤ 2 ∧
      ∀ n ∈ placedActiveCarrierNormals f x, n ∈ Submodule.span ℝ ({p, q} : Set (Space m)) := by
  refine ⟨(Finset.card_image_le).trans
    (placed_activeCarrierAxes_card_le_two_of_boundary_normal_span a f x p q hplanes), ?_⟩
  intro n hn
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  have hi' : (f.symm x) i = 0 ∨ (f.symm x) i = 1 ∨ (f.symm x) i = 2 := by
    simpa [activeCarrierAxes] using hi
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, (f.symm x) i = (k.val : ℝ) := by
    rcases hi' with hi' | hi' | hi'
    · exact ⟨0, by simpa using hi'⟩
    · exact ⟨1, by simpa using hi'⟩
    · exact ⟨2, by simpa using hi'⟩
  exact hplanes (.inl (i, k)) ⟨f.symm x, hk, f.apply_symm_apply x⟩

/-- An exact membership germ is also an exact interior germ on its open ball. -/
theorem centeredGerm_interior_iff {m : ℕ} (S C : Set (Space m))
    (x : Space m) (r : ℝ)
    (heq : ∀ z, ‖z‖ < r → (x + z ∈ S ↔ z ∈ C))
    (z : Space m) (hz : ‖z‖ < r) :
    x + z ∈ interior S ↔ z ∈ interior C := by
  constructor
  · intro hi
    let U : Set (Space m) := {w | x + w ∈ interior S} ∩ Metric.ball 0 r
    have hU : IsOpen U :=
      (isOpen_interior.preimage (continuous_const.add continuous_id)).inter Metric.isOpen_ball
    have hzU : z ∈ U := ⟨hi, by simpa [Metric.mem_ball] using hz⟩
    apply interior_maximal (t := U) _ hU hzU
    intro w hw
    exact (heq w (by simpa [Metric.mem_ball] using hw.2)).mp (interior_subset hw.1)
  · intro hi
    let U : Set (Space m) := {y | y - x ∈ interior C} ∩ Metric.ball x r
    have hU : IsOpen U :=
      (isOpen_interior.preimage (continuous_id.sub continuous_const)).inter Metric.isOpen_ball
    have hzU : x + z ∈ U := ⟨by simpa using hi,
      by simpa [Metric.mem_ball, dist_eq_norm] using hz⟩
    apply interior_maximal (t := U) _ hU hzU
    intro y hy
    have h := (heq (y - x) (by simpa [Metric.mem_ball, dist_eq_norm] using hy.2)).mpr
      (interior_subset hy.1)
    simpa using h

/-- Positive scaling preserves the interiors of sign-determined cones. -/
theorem SignDetermined.smul_mem_interior {m : ℕ} {N : Finset (Space m)}
    {C : Set (Space m)} (h : SignDetermined N C) (t : ℝ) (ht : 0 < t)
    {z : Space m} (hz : z ∈ interior C) : t • z ∈ interior C := by
  let U : Set (Space m) := {w | t⁻¹ • w ∈ interior C}
  have hU : IsOpen U := isOpen_interior.preimage (continuous_const_smul t⁻¹)
  have hzU : t • z ∈ U := by simpa [U, smul_smul, ht.ne'] using hz
  apply interior_maximal (t := U) _ hU hzU
  intro w hw
  have hh := (h.homogeneous t ht (t⁻¹ • w)).mpr (interior_subset hw)
  simpa [smul_smul, ht.ne'] using hh

/-- A vector can be scaled into any specified positive germ ball. -/
theorem exists_pos_smul_norm_lt {m : ℕ} (z : Space m) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ ‖t • z‖ < r := by
  obtain ⟨t, ht, htr⟩ := exists_pos_mul_lt hr ‖z‖
  exact ⟨t, ht, by simpa [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_comm] using htr⟩

end
end PhysicalRegistration.NativeChair
