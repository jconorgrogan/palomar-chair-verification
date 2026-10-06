module

public import SparseMonotiles.KeyBasePlaneAlignment
public import SparseMonotiles.CanonicalRidgeNormals

@[expose] public section

/-!
# Closed two-plane material germs

The base atom is already merged with the carrier atom. Freezing all other
strictly satisfied inequalities leaves the actual bump/dent material as a
closed intersection or union of two halfspaces. In particular, closing a
dent does not leave an artificial membrane on the key base. The closure
argument uses an explicit inward perturbation, rather than distributing
closure over intersections. These statements do not assert a tiling angle
sum or a complete ridge inventory.
-/
namespace SparseMonotiles

open Set Filter
open scoped Topology

section Perturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Keep one inequality fixed while moving strictly into the complement of
another. This is the closure step needed for a base--side dent. -/
theorem closure_nonneg_and_neg_of_perturbation
    (f g : E → ℝ) (hf : Continuous f) (hg : Continuous g)
    (v : E) (c : ℝ) (hc : 0 < c)
    (hvf : ∀ (x : E) (t : ℝ), f (x + t • v) = f x)
    (hvg : ∀ (x : E) (t : ℝ), g (x + t • v) = g x - t * c) :
    closure {x | 0 ≤ f x ∧ g x < 0} = {x | 0 ≤ f x ∧ g x ≤ 0} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro x hx
      exact ⟨hx.1, hx.2.le⟩
    · exact (isClosed_le continuous_const hf).inter (isClosed_le hg continuous_const)
  · intro x hx
    have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
      have hcont : Continuous (fun t : ℝ => x + t • v) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa using (hcont.tendsto (0 : ℝ)).mono_left
        (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    apply mem_closure_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    change 0 ≤ f (x + t • v) ∧ g (x + t • v) < 0
    rw [hvf, hvg]
    exact ⟨hx.1, sub_neg.mpr (lt_of_le_of_lt hx.2 (mul_pos ht hc))⟩

/-- The one-plane case, also used for each branch of a side--side dent. -/
theorem closure_neg_of_perturbation
    (g : E → ℝ) (hg : Continuous g) (v : E) (c : ℝ) (hc : 0 < c)
    (hvg : ∀ (x : E) (t : ℝ), g (x + t • v) = g x - t * c) :
    closure {x | g x < 0} = {x | g x ≤ 0} := by
  simpa using closure_nonneg_and_neg_of_perturbation
    (fun _ : E => (0 : ℝ)) g continuous_const hg v c hc (by simp) hvg

/-- Independence of two real forms supplies a direction tangent to the first
plane and strictly decreasing the second form. -/
theorem exists_inward_of_independent_forms (L M : E →ₗ[ℝ] ℝ)
    (hLM : LinearIndependent ℝ ![L, M]) :
    ∃ v : E, L v = 0 ∧ M v < 0 := by
  have hL : L ≠ 0 := by simpa using hLM.ne_zero (0 : Fin 2)
  obtain ⟨u, hu⟩ : ∃ u, L u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hL (LinearMap.ext h)
  have hex : ∃ v, L v = 0 ∧ M v ≠ 0 := by
    by_contra h
    push_neg at h
    have heq : (M u / L u) • L = M := by
      ext x
      have hv := h (x - (L x / L u) • u)
      have hz : L (x - (L x / L u) • u) = 0 := by
        simp only [map_sub, map_smul, smul_eq_mul]
        field_simp [hu]
        ring
      have hm := hv hz
      change (M u / L u) * L x = M x
      simp only [map_sub, map_smul, smul_eq_mul] at hm ⊢
      field_simp at hm ⊢
      nlinarith
    have hbad := hLM.eq_zero_of_pair' (show (M u / L u) • L = (1 : ℝ) • M by
      simpa using heq)
    norm_num at hbad
  obtain ⟨v, hvL, hvM⟩ := hex
  rcases lt_or_gt_of_ne hvM with hneg | hpos
  · exact ⟨v, hvL, hneg⟩
  · exact ⟨-v, by simp [hvL], by simpa using neg_neg_of_pos hpos⟩

/-- A reusable closed-halfspace intersection identity for independent forms,
including affine offsets. -/
theorem closure_mixed_halfspaces_of_independent
    (L M : E →L[ℝ] ℝ) (hLM : LinearIndependent ℝ ![L.toLinearMap, M.toLinearMap])
    (a b : ℝ) :
    closure {x | a ≤ L x ∧ M x < b} = {x | a ≤ L x ∧ M x ≤ b} := by
  obtain ⟨v, hvL, hvM⟩ := exists_inward_of_independent_forms
    L.toLinearMap M.toLinearMap hLM
  have h := closure_nonneg_and_neg_of_perturbation
    (fun x => L x - a) (fun x => M x - b)
    (L.continuous.sub continuous_const) (M.continuous.sub continuous_const)
    v (-M v) (neg_pos.mpr hvM) ?_ ?_
  · simpa only [sub_nonneg, sub_neg, sub_nonpos] using h
  · intro x t
    simp only [map_add, map_smul, smul_eq_mul]
    change L x + t * L.toLinearMap v - a = L x - a
    rw [hvL, mul_zero, add_zero]
  · intro x t
    simp only [map_add, map_smul, smul_eq_mul]
    ring

/-- The complementary two-plane case closes to the union of the weak
complements. Independence supplies a nonzero inward direction for each. -/
theorem closure_strict_union_of_independent
    (L M : E →L[ℝ] ℝ) (hLM : LinearIndependent ℝ ![L.toLinearMap, M.toLinearMap])
    (a b : ℝ) :
    closure {x | L x < a ∨ M x < b} = {x | L x ≤ a ∨ M x ≤ b} := by
  obtain ⟨v, _, hv⟩ := exists_inward_of_independent_forms
    L.toLinearMap M.toLinearMap hLM
  obtain ⟨w, _, hw⟩ := exists_inward_of_independent_forms
    M.toLinearMap L.toLinearMap (LinearIndependent.pair_symm_iff.mp hLM)
  have hL : closure {x | L x < a} = {x | L x ≤ a} := by
    have h := closure_neg_of_perturbation (fun x => L x - a)
      (L.continuous.sub continuous_const) w (-L w) (neg_pos.mpr hw) ?_
    · simpa only [sub_neg, sub_nonpos] using h
    · intro x t
      simp only [map_add, map_smul, smul_eq_mul]
      ring
  have hM : closure {x | M x < b} = {x | M x ≤ b} := by
    have h := closure_neg_of_perturbation (fun x => M x - b)
      (M.continuous.sub continuous_const) v (-M v) (neg_pos.mpr hv) ?_
    · simpa only [sub_neg, sub_nonpos] using h
    · intro x t
      simp only [map_add, map_smul, smul_eq_mul]
      ring
  change closure ({x | L x < a} ∪ {x | M x < b}) = _
  rw [closure_union, hL, hM]
  rfl

end Perturbation

section TwoPlaneFreezing

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

/-- Physical closed base--side sector. Its two halfspaces form a union for a
bump and an intersection for a dent. -/
def closedBaseSideWedge (slack : ι → X → ℝ) (base side : ι) (b : Bool) : Set X :=
  if b then {x | slack base x ≤ 0 ∨ 0 ≤ slack side x}
  else {x | 0 ≤ slack base x ∧ slack side x ≤ 0}

/-- Physical closed side--side sector. Its two halfspaces form an
intersection for a bump and a union for a dent. -/
def closedSideSideWedge (slack : ι → X → ℝ) (j l : ι) (b : Bool) : Set X :=
  if b then {x | 0 ≤ slack j x ∧ 0 ≤ slack l x}
  else {x | slack j x ≤ 0 ∨ slack l x ≤ 0}

/-- A violated nonbase inequality removes the key locally, leaving precisely
the carrier halfspace. This includes points outside the key footprint. -/
theorem localSetEq_closure_merged_of_nonbase_negative
    (slack : ι → X → ℝ) (base side : ι) (b : Bool) (p : X)
    (hside : side ≠ base) (hf : ∀ i, Continuous (slack i))
    (hneg : slack side p < 0) :
    LocalSetEq p (closure (mergedKeyRegion slack base b))
      (if b then {x | slack base x ≤ 0} else {x | 0 ≤ slack base x}) := by
  have hraw : LocalSetEq p (mergedKeyRegion slack base b)
      (if b then {x | slack base x ≤ 0} else {x | 0 ≤ slack base x}) := by
    filter_upwards [(hf side).continuousAt.eventually (Iio_mem_nhds hneg)] with x hx
    have hn : x ∉ nonbaseHalfspaces slack base := by
      intro h
      exact (not_le_of_gt hx) (h side hside)
    cases b <;> simp [mergedKeyRegion, hn]
  have hc := hraw.closure
  cases b
  · simpa only [Bool.false_eq_true, if_false,
      (isClosed_le continuous_const (hf base)).closure_eq] using hc
  · simpa only [if_true, (isClosed_le (hf base) continuous_const).closure_eq] using hc

/-- On the negative-height side, merged material is already constant, so
closure cannot produce an additional face there. -/
theorem localSetEq_closure_merged_of_base_negative
    (slack : ι → X → ℝ) (base : ι) (b : Bool) (p : X)
    (hf : Continuous (slack base)) (hneg : slack base p < 0) :
    LocalSetEq p (closure (mergedKeyRegion slack base b)) (if b then univ else ∅) := by
  have hraw : LocalSetEq p (mergedKeyRegion slack base b) (if b then univ else ∅) := by
    filter_upwards [hf.continuousAt.eventually (Iio_mem_nhds hneg)] with x hx
    cases b <;> simp [mergedKeyRegion, hx.le, not_le_of_gt hx]
  have hc := hraw.closure
  cases b <;> simpa using hc

theorem not_mem_frontier_of_localSetEq_merged_base_negative
    (slack : ι → X → ℝ) (base : ι) (b : Bool) {p : X} {T : Set X}
    (hf : Continuous (slack base)) (hneg : slack base p < 0)
    (hT : LocalSetEq p T (closure (mergedKeyRegion slack base b))) :
    p ∉ frontier T := by
  have h := (hT.trans (localSetEq_closure_merged_of_base_negative
    slack base b p hf hneg)).frontier.mem_iff
  cases b <;> simpa using h

/-- At a base--side point every omitted nonbase inequality freezes to true. -/
theorem localSetEq_closure_merged_base_side
    (slack : ι → X → ℝ) (base side : ι) (b : Bool) (p : X)
    (hside : side ≠ base) (hf : ∀ i, Continuous (slack i))
    (hother : ∀ i, i ≠ base → i ≠ side → 0 < slack i p)
    (hclose : closure {x | 0 ≤ slack base x ∧ slack side x < 0} =
      {x | 0 ≤ slack base x ∧ slack side x ≤ 0}) :
    LocalSetEq p (closure (mergedKeyRegion slack base b))
      (closedBaseSideWedge slack base side b) := by
  have he : ∀ᶠ x in 𝓝 p, x ∈ nonbaseHalfspaces slack base ↔ 0 ≤ slack side x := by
    apply (eventually_inactive_nonneg slack p (fun i => (hf i).continuousAt)).mono
    intro x hx
    constructor
    · intro h
      exact h side hside
    · intro hs i hi
      by_cases his : i = side
      · simpa [his] using hs
      · exact (hx i (ne_of_gt (hother i hi his))).mpr (hother i hi his).le
  have hraw : LocalSetEq p (mergedKeyRegion slack base b)
      (if b then {x | slack base x ≤ 0 ∨ 0 ≤ slack side x}
        else {x | 0 ≤ slack base x ∧ slack side x < 0}) := by
    apply he.mono
    intro x hx
    cases b <;> simp [mergedKeyRegion, hx, not_le]
  have hclosed := hraw.closure
  cases b
  · simpa only [Bool.false_eq_true, if_false, closedBaseSideWedge, hclose] using hclosed
  · have hc : IsClosed {x | slack base x ≤ 0 ∨ 0 ≤ slack side x} :=
      (isClosed_le (hf base) continuous_const).union
        (isClosed_le continuous_const (hf side))
    simpa only [if_true, closedBaseSideWedge, hc.closure_eq] using hclosed

/-- Away from the base, two nonbase atoms are all that remain. Taking closure
turns the strict complement into the union of the two closed complements. -/
theorem localSetEq_closure_merged_side_side
    (slack : ι → X → ℝ) (base j l : ι) (b : Bool) (p : X)
    (hj : j ≠ base) (hl : l ≠ base) (hf : ∀ i, Continuous (slack i))
    (hbase : 0 < slack base p)
    (hother : ∀ i, i ≠ base → i ≠ j → i ≠ l → 0 < slack i p)
    (hclosej : closure {x | slack j x < 0} = {x | slack j x ≤ 0})
    (hclosel : closure {x | slack l x < 0} = {x | slack l x ≤ 0}) :
    LocalSetEq p (closure (mergedKeyRegion slack base b))
      (closedSideSideWedge slack j l b) := by
  have he : ∀ᶠ x in 𝓝 p, 0 < slack base x ∧
      (x ∈ nonbaseHalfspaces slack base ↔ 0 ≤ slack j x ∧ 0 ≤ slack l x) := by
    filter_upwards [(hf base).continuousAt.eventually (Ioi_mem_nhds hbase),
      eventually_inactive_nonneg slack p (fun i => (hf i).continuousAt)] with x hx hix
    refine ⟨hx, ?_⟩
    constructor
    · intro h
      exact ⟨h j hj, h l hl⟩
    · rintro ⟨hjx, hlx⟩ i hi
      by_cases hij : i = j
      · simpa [hij] using hjx
      by_cases hil : i = l
      · simpa [hil] using hlx
      exact (hix i (ne_of_gt (hother i hi hij hil))).mpr (hother i hi hij hil).le
  have hraw : LocalSetEq p (mergedKeyRegion slack base b)
      (if b then {x | 0 ≤ slack j x ∧ 0 ≤ slack l x}
        else {x | slack j x < 0 ∨ slack l x < 0}) := by
    apply he.mono
    intro x hx
    cases b
    · simp only [mergedKeyRegion, Bool.false_eq_true, if_false, Set.mem_setOf_eq,
        hx.2, hx.1.le, true_and, not_and_or, not_le]
    · simp [mergedKeyRegion, hx.2, not_le_of_gt hx.1]
  have hclosed := hraw.closure
  cases b
  · have hc : closure {x | slack j x < 0 ∨ slack l x < 0} =
        {x | slack j x ≤ 0 ∨ slack l x ≤ 0} := by
      change closure ({x | slack j x < 0} ∪ {x | slack l x < 0}) = _
      rw [closure_union, hclosej, hclosel]
      rfl
    simpa only [Bool.false_eq_true, if_false, closedSideSideWedge, hc] using hclosed
  · have hc : IsClosed {x | 0 ≤ slack j x ∧ 0 ≤ slack l x} :=
      (isClosed_le continuous_const (hf j)).inter
        (isClosed_le continuous_const (hf l))
    simpa only [if_true, closedSideSideWedge, hc.closure_eq] using hclosed

end TwoPlaneFreezing

section KeyPerturbation

/-- A signed tangential displacement increases exactly the chosen outward
side form, and does not move the base coordinate. -/
noncomputable def keySideOutwardDirection {n : ℕ} (i : Fin n) (b : Bool) :
    Point (n + 1) := EuclideanSpace.single i.castSucc (if b then 1 else -1)

@[simp] theorem keySideOutwardDirection_last {n : ℕ} (i : Fin n) (b : Bool) :
    keySideOutwardDirection i b (Fin.last n) = 0 := by
  simp [keySideOutwardDirection, EuclideanSpace.single_apply,
    Ne.symm (Fin.castSucc_ne_last i)]

@[simp] theorem keySideOutwardDirection_same {n : ℕ} (i : Fin n) (b : Bool) :
    keySideOutwardDirection i b i.castSucc = if b then 1 else -1 := by
  simp [keySideOutwardDirection, EuclideanSpace.single_apply]

/-- The exact actual side slack decreases under the explicit perturbation. -/
theorem keyPyramidSideSlack_perturbation {n : ℕ} (k : KeyData (n + 1))
    (i : Fin n) (b : Bool) (x : Point (n + 1)) (t : ℝ) :
    keyPyramidHalfspaceSlack k (.inr (i, b)) (x + t • keySideOutwardDirection i b) =
      keyPyramidHalfspaceSlack k (.inr (i, b)) x - t * keyPyramidHeight k := by
  simp only [keyPyramidHalfspaceSlack, map_add, map_smul, smul_eq_mul]
  have hv : keyPyramidHalfspaceNormal k (.inr (i, b))
      (keySideOutwardDirection i b) = keyPyramidHeight k := by
    rw [keyPyramidHalfspaceNormal_apply]
    cases b <;> simp
  rw [hv]
  ring

/-- Closing the genuine base--side dent adds precisely the two weak faces. -/
theorem closure_key_base_side_dent {n : ℕ} (k : KeyData (n + 1))
    (hh : 0 < keyPyramidHeight k) (i : Fin n) (b : Bool) :
    closure {x | 0 ≤ keyPyramidHalfspaceSlack k (.inl false) x ∧
      keyPyramidHalfspaceSlack k (.inr (i, b)) x < 0} =
      {x | 0 ≤ keyPyramidHalfspaceSlack k (.inl false) x ∧
        keyPyramidHalfspaceSlack k (.inr (i, b)) x ≤ 0} := by
  apply closure_nonneg_and_neg_of_perturbation
    (keyPyramidHalfspaceSlack k (.inl false)) (keyPyramidHalfspaceSlack k (.inr (i, b)))
    (continuous_keyPyramidHalfspaceSlack k _) (continuous_keyPyramidHalfspaceSlack k _)
    (keySideOutwardDirection i b) (keyPyramidHeight k) hh
  · intro x t
    simp
  · exact keyPyramidSideSlack_perturbation k i b

/-- Each strict side complement closes to its weak halfspace. -/
theorem closure_key_side_negative {n : ℕ} (k : KeyData (n + 1))
    (hh : 0 < keyPyramidHeight k) (i : Fin n) (b : Bool) :
    closure {x | keyPyramidHalfspaceSlack k (.inr (i, b)) x < 0} =
      {x | keyPyramidHalfspaceSlack k (.inr (i, b)) x ≤ 0} := by
  exact closure_neg_of_perturbation _ (continuous_keyPyramidHalfspaceSlack k _)
    (keySideOutwardDirection i b) (keyPyramidHeight k) hh
    (keyPyramidSideSlack_perturbation k i b)

/-- Closure commutes with a canonical rigid pose, so the perturbation result
is about physical coordinates as well as reference coordinates. -/
theorem closure_key_base_side_dent_posed {n : ℕ} (k : KeyData (n + 1))
    (hh : 0 < keyPyramidHeight k) (p : Contact.Pose (n + 1)) (i : Fin n) (b : Bool) :
    closure {x | 0 ≤ keyPyramidHalfspaceSlack k (.inl false) (p.euclidean.symm x) ∧
      keyPyramidHalfspaceSlack k (.inr (i, b)) (p.euclidean.symm x) < 0} =
      {x | 0 ≤ keyPyramidHalfspaceSlack k (.inl false) (p.euclidean.symm x) ∧
        keyPyramidHalfspaceSlack k (.inr (i, b)) (p.euclidean.symm x) ≤ 0} := by
  change closure (p.euclidean.symm.toHomeomorph ⁻¹'
      {x | 0 ≤ keyPyramidHalfspaceSlack k (.inl false) x ∧
        keyPyramidHalfspaceSlack k (.inr (i, b)) x < 0}) =
    p.euclidean.symm.toHomeomorph ⁻¹'
      {x | 0 ≤ keyPyramidHalfspaceSlack k (.inl false) x ∧
        keyPyramidHalfspaceSlack k (.inr (i, b)) x ≤ 0}
  rw [← Homeomorph.preimage_closure, closure_key_base_side_dent k hh]

theorem closure_key_side_negative_posed {n : ℕ} (k : KeyData (n + 1))
    (hh : 0 < keyPyramidHeight k) (p : Contact.Pose (n + 1)) (i : Fin n) (b : Bool) :
    closure {x | keyPyramidHalfspaceSlack k (.inr (i, b)) (p.euclidean.symm x) < 0} =
      {x | keyPyramidHalfspaceSlack k (.inr (i, b)) (p.euclidean.symm x) ≤ 0} := by
  change closure (p.euclidean.symm.toHomeomorph ⁻¹'
      {x | keyPyramidHalfspaceSlack k (.inr (i, b)) x < 0}) =
    p.euclidean.symm.toHomeomorph ⁻¹'
      {x | keyPyramidHalfspaceSlack k (.inr (i, b)) x ≤ 0}
  rw [← Homeomorph.preimage_closure, closure_key_side_negative k hh]

/-- At an actual key point away from the apex, exactly two active inequalities
produce a base--side or a distinct-axis side--side closed material wedge.
Strictness of every omitted inequality is derived from actual key membership
and the exact active-plane inventory; it is not a separate geometric premise. -/
theorem localSetEq_closed_wedge_of_two_active_key_planes {n : ℕ}
    (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k)
    (hwidth : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    (q : Contact.Pose (n + 1)) (bump : Bool)
    {p : Point (n + 1)} {T : Set (Point (n + 1))}
    (hp : q.euclidean.symm p ∈ keySolid k)
    (hne : q.euclidean.symm p ≠ rationalPoint k.apex)
    {j l : PyramidHalfspaceIndex n} (hjl : j ≠ l)
    (hj : keyPyramidHalfspaceSlack k j (q.euclidean.symm p) = 0)
    (hl : keyPyramidHalfspaceSlack k l (q.euclidean.symm p) = 0)
    (hother : ∀ m, m ≠ j → m ≠ l →
      keyPyramidHalfspaceSlack k m (q.euclidean.symm p) ≠ 0)
    (hT : LocalSetEq p T (closure (mergedKeyRegion
      (fun m x => keyPyramidHalfspaceSlack k m (q.euclidean.symm x)) (.inl false) bump))) :
    (∃ i si, LocalSetEq p T (closedBaseSideWedge
      (fun m x => keyPyramidHalfspaceSlack k m (q.euclidean.symm x))
        (.inl false) (.inr (i, si)) bump)) ∨
    (∃ i r si sr, i ≠ r ∧ LocalSetEq p T (closedSideSideWedge
      (fun m x => keyPyramidHalfspaceSlack k m (q.euclidean.symm x))
        (.inr (i, si)) (.inr (r, sr)) bump)) := by
  have hcont (m : PyramidHalfspaceIndex n) :
      Continuous (fun x => keyPyramidHalfspaceSlack k m (q.euclidean.symm x)) :=
    (continuous_keyPyramidHalfspaceSlack k m).comp q.euclidean.symm.continuous
  have hnonneg := (mem_keySolid_iff_nonneg_slacks k hc hr hh _).mp hp
  have hpos (m : PyramidHalfspaceIndex n) (hmj : m ≠ j) (hml : m ≠ l) :
      0 < keyPyramidHalfspaceSlack k m (q.euclidean.symm p) :=
    lt_of_le_of_ne (hnonneg m) (Ne.symm (hother m hmj hml))
  obtain ⟨a, c, ha, hc', hpair⟩ := active_key_halfspace_pair_classification
    k hc hr hh hwidth hp hne hjl hj hl
  cases a with
  | none =>
      cases c with
      | none => exact (show False from hpair).elim
      | some s =>
          rcases s with ⟨i, si⟩
          simp only [pyramidFacetHalfspaceIndex] at ha hc'
          subst j l
          refine Or.inl ⟨i, si, hT.trans ?_⟩
          apply localSetEq_closure_merged_base_side _ _ _ _ _ (by simp) hcont
          · intro m hm0 hmi
            exact hpos m hm0 hmi
          · exact closure_key_base_side_dent_posed k hh q i si
  | some s =>
      rcases s with ⟨i, si⟩
      cases c with
      | none =>
          simp only [pyramidFacetHalfspaceIndex] at ha hc'
          subst j l
          refine Or.inl ⟨i, si, hT.trans ?_⟩
          apply localSetEq_closure_merged_base_side _ _ _ _ _ (by simp) hcont
          · intro m hm0 hmi
            exact hpos m hmi hm0
          · exact closure_key_base_side_dent_posed k hh q i si
      | some t =>
          rcases t with ⟨r, sr⟩
          simp only [pyramidFacetHalfspaceIndex] at ha hc'
          subst j l
          refine Or.inr ⟨i, r, si, sr, hpair, hT.trans ?_⟩
          apply localSetEq_closure_merged_side_side _ _ _ _ _ _ (by simp) (by simp)
            hcont (hpos (.inl false) (by simp) (by simp))
          · intro m _ hmi hmr
            exact hpos m hmi hmr
          · exact closure_key_side_negative_posed k hh q i si
          · exact closure_key_side_negative_posed k hh q r sr

end KeyPerturbation

namespace Canonical

/-- The actual posed five-dimensional merged germ at a base--side ridge is
exactly its closed two-halfspace material sector. -/
theorem localSetEq_base_side_wedge5 (q : Contact.Pose 5) (i : Fin 4)
    (sideSign b : Bool) {p : Point 5} {T : Set (Point 5)}
    (hother : ∀ j : PyramidHalfspaceIndex 4,
      j ≠ .inl false → j ≠ .inr (i, sideSign) → 0 < posedHalfspaceSlack5 q j p)
    (hT : LocalSetEq p T
      (closure (mergedKeyRegion (posedHalfspaceSlack5 q) (.inl false) b))) :
    LocalSetEq p T
      (closedBaseSideWedge (posedHalfspaceSlack5 q) (.inl false) (.inr (i, sideSign)) b) := by
  apply hT.trans
  apply localSetEq_closure_merged_base_side _ _ _ _ _ (by simp)
    (continuous_posedHalfspaceSlack5 q) hother
  apply closure_key_base_side_dent_posed
  change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
  rw [referenceBox5_height]
  norm_num

theorem localSetEq_base_side_wedge7 (q : Contact.Pose 7) (i : Fin 6)
    (sideSign b : Bool) {p : Point 7} {T : Set (Point 7)}
    (hother : ∀ j : PyramidHalfspaceIndex 6,
      j ≠ .inl false → j ≠ .inr (i, sideSign) → 0 < posedHalfspaceSlack7 q j p)
    (hT : LocalSetEq p T
      (closure (mergedKeyRegion (posedHalfspaceSlack7 q) (.inl false) b))) :
    LocalSetEq p T
      (closedBaseSideWedge (posedHalfspaceSlack7 q) (.inl false) (.inr (i, sideSign)) b) := by
  apply hT.trans
  apply localSetEq_closure_merged_base_side _ _ _ _ _ (by simp)
    (continuous_posedHalfspaceSlack7 q) hother
  apply closure_key_base_side_dent_posed
  change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
  rw [referenceBox7_height]
  norm_num

/-- The side--side closure step needs only genuine side forms. The separate
active-plane classification supplies distinct axes away from the apex. -/
theorem localSetEq_side_side_wedge5 (q : Contact.Pose 5) (i j : Fin 4)
    (si sj b : Bool) {p : Point 5} {T : Set (Point 5)}
    (hbase : 0 < posedHalfspaceSlack5 q (.inl false) p)
    (hother : ∀ l : PyramidHalfspaceIndex 4,
      l ≠ .inl false → l ≠ .inr (i, si) → l ≠ .inr (j, sj) →
        0 < posedHalfspaceSlack5 q l p)
    (hT : LocalSetEq p T
      (closure (mergedKeyRegion (posedHalfspaceSlack5 q) (.inl false) b))) :
    LocalSetEq p T
      (closedSideSideWedge (posedHalfspaceSlack5 q) (.inr (i, si)) (.inr (j, sj)) b) := by
  apply hT.trans
  apply localSetEq_closure_merged_side_side _ _ _ _ _ _ (by simp) (by simp)
    (continuous_posedHalfspaceSlack5 q) hbase hother
  all_goals
    apply closure_key_side_negative_posed
    change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
    rw [referenceBox5_height]
    norm_num

theorem localSetEq_side_side_wedge7 (q : Contact.Pose 7) (i j : Fin 6)
    (si sj b : Bool) {p : Point 7} {T : Set (Point 7)}
    (hbase : 0 < posedHalfspaceSlack7 q (.inl false) p)
    (hother : ∀ l : PyramidHalfspaceIndex 6,
      l ≠ .inl false → l ≠ .inr (i, si) → l ≠ .inr (j, sj) →
        0 < posedHalfspaceSlack7 q l p)
    (hT : LocalSetEq p T
      (closure (mergedKeyRegion (posedHalfspaceSlack7 q) (.inl false) b))) :
    LocalSetEq p T
      (closedSideSideWedge (posedHalfspaceSlack7 q) (.inr (i, si)) (.inr (j, sj)) b) := by
  apply hT.trans
  apply localSetEq_closure_merged_side_side _ _ _ _ _ _ (by simp) (by simp)
    (continuous_posedHalfspaceSlack7 q) hbase hother
  all_goals
    apply closure_key_side_negative_posed
    change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
    rw [referenceBox7_height]
    norm_num

end Canonical

#print axioms closure_nonneg_and_neg_of_perturbation
#print axioms exists_inward_of_independent_forms
#print axioms closure_strict_union_of_independent
#print axioms closure_mixed_halfspaces_of_independent
#print axioms localSetEq_closure_merged_base_side
#print axioms localSetEq_closure_merged_side_side
#print axioms closure_key_base_side_dent_posed
#print axioms closure_key_side_negative_posed
#print axioms localSetEq_closed_wedge_of_two_active_key_planes
#print axioms localSetEq_closure_merged_of_nonbase_negative
#print axioms localSetEq_closure_merged_of_base_negative
#print axioms not_mem_frontier_of_localSetEq_merged_base_negative
#print axioms Canonical.localSetEq_base_side_wedge5
#print axioms Canonical.localSetEq_base_side_wedge7
#print axioms Canonical.localSetEq_side_side_wedge5
#print axioms Canonical.localSetEq_side_side_wedge7

end SparseMonotiles
