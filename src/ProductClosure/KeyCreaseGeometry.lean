module

public import ProductClosure.IsometryTransport

@[expose] public section

/-!
# Literal side faces and normal invariants of the native key

The affine branches are extracted from the actual zero-extended max-min
height.  Their graph pieces, base creases and distinct-axis side creases are
concrete subsets of the already constructed native key graph.  This module
computes the normal-angle invariants of their defining affine planes; it does
not yet assert a complete boundary-stratum inventory or a contact theorem.
-/

namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

/-- A negative or positive side of one tangent coordinate. -/
abbrev Side (m : ℕ) := Fin m × Bool

/-- `false` is the negative-coordinate side; `true` the positive side. -/
def sidePrime  (J : ℕ) (s : Side m) : ℕ :=
  keyPrime J (2 * s.1.val + if s.2 then 1 else 0)

def sideSign  (s : Side m) : ℝ := if s.2 then -1 else 1

def branchProfile  (J : ℕ) (u : Site S) (s : Side m)
    (x : Space m) : ℝ :=
  1 + sideSign s * (sidePrime J s : ℝ) * tangentCoord u x s.1 / eta m

def sideSlope {J : ℕ} (a : Coefficients S J) (u : Site S) (s : Side m) : ℝ :=
  (a.value u : ℝ) * sideSign s * (sidePrime J s : ℝ) / denominator m J

def sideHeight {J : ℕ} (a : Coefficients S J) (u : Site S) (s : Side m)
    (x : Space m) : ℝ :=
  eta m * (a.value u : ℝ) / denominator m J + sideSlope a u s * tangentCoord u x s.1

/-- A branch contributes precisely where it is nonnegative and minimal. -/
def branchRegion  (J : ℕ) (u : Site S) (s : Side m) : Set (Space m) :=
  {x | 0 ≤ branchProfile J u s x ∧ ∀ t, branchProfile J u s x ≤ branchProfile J u t x}

theorem branchProfile_false  (J : ℕ) (u : Site S) (i : Fin m) (x : Space m) :
    branchProfile J u (i, false) x = 1 + pMinus J i * tangentCoord u x i / eta m := by
  simp [branchProfile, sideSign, sidePrime, pMinus]

theorem branchProfile_true  (J : ℕ) (u : Site S) (i : Fin m) (x : Space m) :
    branchProfile J u (i, true) x = 1 - pPlus J i * tangentCoord u x i / eta m := by
  simp [branchProfile, sideSign, sidePrime, pPlus]
  ring

theorem native_profile_eq_branch  [NeZero m] (J : ℕ) (u : Site S)
    (s : Side m) (x : Space m) (hx : x ∈ branchRegion J u s) :
    keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) (x - siteCenter u) =
      branchProfile J u s x := by
  have hlo : ∀ i : Fin m,
      branchProfile J u s x ≤ min
        (1 + pMinus J i * tangentCoord u x i / eta m)
        (1 - pPlus J i * tangentCoord u x i / eta m) := by
    intro i
    exact le_min (by simpa only [branchProfile_false] using hx.2 (i, false))
      (by simpa only [branchProfile_true] using hx.2 (i, true))
  have hlower : branchProfile J u s x ≤
      finiteLowerEnvelope (fun i y =>
        min (1 + pMinus J i * ⟪siteAxis u i, y⟫_ℝ / eta m)
          (1 - pPlus J i * ⟪siteAxis u i, y⟫_ℝ / eta m)) (x - siteCenter u) := by
    apply Finset.le_inf'
    intro i _
    exact hlo i
  have hupper := finiteLowerEnvelope_le (fun i y =>
        min (1 + pMinus J i * ⟪siteAxis u i, y⟫_ℝ / eta m)
          (1 - pPlus J i * ⟪siteAxis u i, y⟫_ℝ / eta m)) (x - siteCenter u) s.1
  have heq : finiteLowerEnvelope (fun i y =>
        min (1 + pMinus J i * ⟪siteAxis u i, y⟫_ℝ / eta m)
          (1 - pPlus J i * ⟪siteAxis u i, y⟫_ℝ / eta m)) (x - siteCenter u) =
      branchProfile J u s x := by
    apply le_antisymm _ hlower
    rcases s with ⟨i, b⟩
    cases b
    · rw [branchProfile_false]
      exact hupper.trans (min_le_left _ _)
    · rw [branchProfile_true]
      exact hupper.trans (min_le_right _ _)
  unfold keyTentProfile
  rw [heq, max_eq_right hx.1]

/-- No facet equation is assumed: the affine branch follows from the literal tent. -/
theorem siteHeight_eq_sideHeight {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) (s : Side m) (x : Space m) (hx : x ∈ branchRegion J u s) :
    siteHeight a u x = sideHeight a u s x := by
  unfold siteHeight keyHeight
  rw [native_profile_eq_branch J u s x hx]
  unfold branchProfile sideHeight sideSlope
  have he : eta m ≠ 0 := (eta_pos m).ne'
  field_simp

/-- Tube footprints lie in the nonnegative region of every actual branch. -/
theorem branchProfile_nonneg_of_mem_closedTube  (J : ℕ) (u : Site S)
    (s : Side m) (x : Space m) (hx : x ∈ closedTube J u) :
    0 ≤ branchProfile J u s x := by
  rcases s with ⟨i, b⟩
  have he := eta_pos m
  cases b
  · rw [branchProfile_false]
    have h := (div_le_iff₀ (pMinus_pos J i)).mp (hx.2 i).1
    have hdiv : -1 ≤ pMinus J i * tangentCoord u x i / eta m :=
      (le_div_iff₀ he).mpr (by nlinarith)
    linarith
  · rw [branchProfile_true]
    have h := (le_div_iff₀ (pPlus_pos J i)).mp (hx.2 i).2
    have hdiv : pPlus J i * tangentCoord u x i / eta m ≤ 1 :=
      (div_le_iff₀ he).mpr (by nlinarith)
    linarith

/-- Every tube point has an active branch. This is a finite minimum argument,
not a supplied facet-coverage hypothesis. -/
theorem exists_active_branch  [NeZero m] (J : ℕ) (u : Site S)
    (x : Space m) (hx : x ∈ closedTube J u) :
    ∃ s : Side m, x ∈ branchRegion J u s := by
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Side m))
    (fun s => branchProfile J u s x)
  refine ⟨s, branchProfile_nonneg_of_mem_closedTube J u s x hx, ?_⟩
  intro t
  rw [← hs]
  exact Finset.inf'_le _ (Finset.mem_univ t)

/-- Unnormalized outward normal of the actual affine side branch. -/
def sideNormal {J : ℕ} (a : Coefficients S J) (u : Site S) (s : Side m) : Space m :=
  outward u.1 - sideSlope a u s • siteAxis u s.1

/-- The closed graph piece selected by one branch of the native key. -/
def sideFace {J : ℕ} [NeZero m] (a : Coefficients S J) (u : Site S)
    (s : Side m) : Set (Space m) := keyGraph a u ∩ branchRegion J u s

/-- Where an affine side face meets the zero-height carrier plane. -/
def baseCrease {J : ℕ} [NeZero m] (a : Coefficients S J) (u : Site S)
    (s : Side m) : Set (Space m) := sideFace a u s ∩ {x | normalCoord u x = 0}

/-- Distinct tangent axes give the side-side crease class in the manuscript. -/
def sideCrease {J : ℕ} [NeZero m] (a : Coefficients S J) (u : Site S)
    (s t : Side m) : Set (Space m) := sideFace a u s ∩ sideFace a u t

theorem sideFace_plane {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) (s : Side m) (x : Space m) (hx : x ∈ sideFace a u s) :
    ⟪sideNormal a u s, x - siteCenter u⟫_ℝ =
      eta m * (a.value u : ℝ) / denominator m J := by
  have hh := siteHeight_eq_sideHeight a u s x hx.2
  have hg := hx.1.2
  simp only [sideNormal, inner_sub_left, real_inner_smul_left]
  change normalCoord u x - sideSlope a u s * tangentCoord u x s.1 = _
  rw [hg, hh]
  simp [sideHeight]

/-- The whole literal key graph is the union of its finitely many affine sides. -/
theorem keyGraph_eq_iUnion_sideFace {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) : keyGraph a u = ⋃ s : Side m, sideFace a u s := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := exists_active_branch J u x hx.1
    exact mem_iUnion.mpr ⟨s, hx, hs⟩
  · intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    exact hs.1

theorem branchProfile_continuous  (J : ℕ) (u : Site S) (s : Side m) :
    Continuous (branchProfile J u s) := by
  unfold branchProfile tangentCoord
  fun_prop

theorem branchRegion_isClosed  (J : ℕ) (u : Site S) (s : Side m) :
    IsClosed (branchRegion J u s) := by
  unfold branchRegion
  simp only [ofPred_and, ofPred_forall]
  exact (isClosed_le continuous_const (branchProfile_continuous J u s)).inter
    (isClosed_iInter (fun t => isClosed_le
      (branchProfile_continuous J u s) (branchProfile_continuous J u t)))

theorem keyGraph_isCompact {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) : IsCompact (keyGraph a u) := by
  have hH : Continuous (siteHeight a u) := by
    let L : NNReal := ⟨(J : ℝ) * pMax m J / denominator m J, by positivity⟩
    have hLip : LipschitzWith L (siteHeight a u) := lipschitzWith_iff_norm_sub_le.mpr
      (by
        intro x y
        change ‖siteHeight a u x - siteHeight a u y‖ ≤
          ((J : ℝ) * pMax m J / denominator m J) * ‖x - y‖
        simpa only [Real.norm_eq_abs] using siteHeight_lipschitz a u x y)
    exact hLip.continuous
  apply (closedTube_isCompact J u).inter_right
  exact isClosed_eq (by unfold normalCoord; fun_prop) hH

theorem sideFace_isCompact {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) (s : Side m) : IsCompact (sideFace a u s) :=
  (keyGraph_isCompact a u).inter_right (branchRegion_isClosed J u s)

theorem baseCrease_isCompact {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) (s : Side m) : IsCompact (baseCrease a u s) :=
  (sideFace_isCompact a u s).inter_right (isClosed_eq
    (by unfold normalCoord; fun_prop) continuous_const)

theorem sideCrease_isCompact {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) (s t : Side m) : IsCompact (sideCrease a u s t) :=
  (sideFace_isCompact a u s).inter_right (sideFace_isCompact a u t).isClosed

/-- The manuscript's closed complex: base-side intersections and side-side
intersections from distinct tangent axes. Lower-dimensional boundaries are kept. -/
def creaseComplex {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) : Set (Space m) :=
  (⋃ s : Side m, baseCrease a u s) ∪
    ⋃ (s : Side m) (t : {t : Side m // s.1 ≠ t.1}), sideCrease a u s t.val

theorem creaseComplex_subset_keyGraph {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) : creaseComplex a u ⊆ keyGraph a u := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    exact hs.1.1
  · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    obtain ⟨t, ht⟩ := mem_iUnion.mp hs
    exact ht.1.1

theorem creaseComplex_isCompact {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) : IsCompact (creaseComplex a u) := by
  exact (isCompact_iUnion (baseCrease_isCompact a u)).union
    (isCompact_iUnion fun s => isCompact_iUnion fun t => sideCrease_isCompact a u s t.val)

/-- Squared cosine of the unoriented angle between two nonzero normal lines.
It is unchanged by reversing either normal, so it is suitable for complementary
material sectors. Its use does not assume a contact or a companion. -/
def normalCosSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : E) : ℝ := ⟪v, w⟫_ℝ ^ 2 / (⟪v, v⟫_ℝ * ⟪w, w⟫_ℝ)

theorem sideNormal_inner_outward {J : ℕ} (a : Coefficients S J)
    (u : Site S) (s : Side m) : ⟪sideNormal a u s, outward u.1⟫_ℝ = 1 := by
  simp [sideNormal, inner_sub_left, real_inner_smul_left]

theorem sideNormal_inner_self {J : ℕ} (a : Coefficients S J)
    (u : Site S) (s : Side m) :
    ⟪sideNormal a u s, sideNormal a u s⟫_ℝ = 1 + sideSlope a u s ^ 2 := by
  have horth : ⟪outward u.1, siteAxis u s.1⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact siteAxis_outward_inner u s.1
  unfold sideNormal
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  simp only [real_inner_smul_left, real_inner_smul_right]
  simp [horth, pow_two]

theorem sideNormal_ne_zero {J : ℕ} (a : Coefficients S J)
    (u : Site S) (s : Side m) : sideNormal a u s ≠ 0 := by
  intro hz
  have h := sideNormal_inner_outward a u s
  simp [hz] at h

theorem base_normalCosSq {J : ℕ} (a : Coefficients S J)
    (u : Site S) (s : Side m) :
    normalCosSq (sideNormal a u s) (outward u.1) =
      1 / (1 + sideSlope a u s ^ 2) := by
  unfold normalCosSq
  rw [sideNormal_inner_outward, sideNormal_inner_self]
  simp

theorem sideNormal_inner_of_distinct_axes {J : ℕ} (a : Coefficients S J)
    (u : Site S) (s t : Side m) (hst : s.1 ≠ t.1) :
    ⟪sideNormal a u s, sideNormal a u t⟫_ℝ = 1 := by
  have horth : ⟪outward u.1, siteAxis u t.1⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact siteAxis_outward_inner u t.1
  simp [sideNormal, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, horth, siteAxis_inner, hst]

theorem side_normalCosSq {J : ℕ} (a : Coefficients S J)
    (u : Site S) (s t : Side m) (hst : s.1 ≠ t.1) :
    normalCosSq (sideNormal a u s) (sideNormal a u t) =
      1 / ((1 + sideSlope a u s ^ 2) * (1 + sideSlope a u t ^ 2)) := by
  unfold normalCosSq
  rw [sideNormal_inner_of_distinct_axes a u s t hst,
    sideNormal_inner_self, sideNormal_inner_self]
  norm_num

theorem normalCosSq_map {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E ≃ₗᵢ[ℝ] F) (v w : E) : normalCosSq (f v) (f w) = normalCosSq v w := by
  simp [normalCosSq]

end
end ProductClosure.NativeCompiler
