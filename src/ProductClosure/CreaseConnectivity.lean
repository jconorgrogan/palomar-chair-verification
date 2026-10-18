module

public import ProductClosure.KeyCreaseGeometry
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section

/-!
# Connectedness of the literal native key crease complex

The pieces here are the actual max-min graph pieces defined in
`KeyCreaseGeometry`. Their convexity, a common apex, and explicit footprint
vertices supply all incidence facts used in the connectedness proof.
-/

namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {C : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell C)]

private theorem centered_combination  (u : Site C) (x y : Space m)
    (r q : ℝ) (hrq : r + q = 1) :
    r • x + q • y - siteCenter u =
      r • (x - siteCenter u) + q • (y - siteCenter u) := by
  rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hrq, one_smul]

theorem normalCoord_combination  (u : Site C) (x y : Space m)
    (r q : ℝ) (hrq : r + q = 1) :
    normalCoord u (r • x + q • y) = r * normalCoord u x + q * normalCoord u y := by
  simp only [normalCoord, centered_combination u x y r q hrq,
    inner_add_right, real_inner_smul_right]

theorem tangentCoord_combination  (u : Site C) (x y : Space m)
    (r q : ℝ) (hrq : r + q = 1) (i : Fin m) :
    tangentCoord u (r • x + q • y) i =
      r * tangentCoord u x i + q * tangentCoord u y i := by
  simp only [tangentCoord, centered_combination u x y r q hrq,
    inner_add_right, real_inner_smul_right]

theorem branchProfile_combination  (J : ℕ) (u : Site C) (s : Side m)
    (x y : Space m) (r q : ℝ) (hrq : r + q = 1) :
    branchProfile J u s (r • x + q • y) =
      r * branchProfile J u s x + q * branchProfile J u s y := by
  unfold branchProfile
  rw [tangentCoord_combination u x y r q hrq]
  have hq : q = 1 - r := by linarith
  rw [hq]
  ring

theorem sideHeight_combination {J : ℕ} (a : Coefficients C J) (u : Site C)
    (s : Side m) (x y : Space m) (r q : ℝ) (hrq : r + q = 1) :
    sideHeight a u s (r • x + q • y) =
      r * sideHeight a u s x + q * sideHeight a u s y := by
  unfold sideHeight
  rw [tangentCoord_combination u x y r q hrq]
  have hq : q = 1 - r := by linarith
  rw [hq]
  ring

theorem closedTube_convex  (J : ℕ) (u : Site C) :
    Convex ℝ (closedTube J u) := by
  intro x hx y hy r q hr hq hrq
  refine ⟨?_, fun i => ?_⟩
  · rw [normalCoord_combination u x y r q hrq]
    exact abs_le.mpr (convex_Icc (-rho m) (rho m) (abs_le.mp hx.1)
      (abs_le.mp hy.1) hr hq hrq)
  · rw [tangentCoord_combination u x y r q hrq]
    exact convex_Icc (-eta m / pMinus J i) (eta m / pPlus J i)
      (hx.2 i) (hy.2 i) hr hq hrq

theorem branchRegion_convex  (J : ℕ) (u : Site C) (s : Side m) :
    Convex ℝ (branchRegion J u s) := by
  intro x hx y hy r q hr hq hrq
  constructor
  · rw [branchProfile_combination J u s x y r q hrq]
    exact add_nonneg (mul_nonneg hr hx.1) (mul_nonneg hq hy.1)
  · intro t
    rw [branchProfile_combination J u s x y r q hrq,
      branchProfile_combination J u t x y r q hrq]
    exact add_le_add (mul_le_mul_of_nonneg_left (hx.2 t) hr)
      (mul_le_mul_of_nonneg_left (hy.2 t) hq)

theorem sideFace_convex {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s : Side m) : Convex ℝ (sideFace a u s) := by
  intro x hx y hy r q hr hq hrq
  have hreg := branchRegion_convex J u s hx.2 hy.2 hr hq hrq
  refine ⟨⟨closedTube_convex J u hx.1.1 hy.1.1 hr hq hrq, ?_⟩, hreg⟩
  rw [siteHeight_eq_sideHeight a u s _ hreg,
    normalCoord_combination u x y r q hrq,
    sideHeight_combination a u s x y r q hrq,
    hx.1.2, hy.1.2, siteHeight_eq_sideHeight a u s x hx.2,
    siteHeight_eq_sideHeight a u s y hy.2]

theorem baseCrease_convex {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s : Side m) : Convex ℝ (baseCrease a u s) := by
  apply (sideFace_convex a u s).inter
  intro x hx y hy r q _ _ hrq
  change normalCoord u (r • x + q • y) = 0
  rw [normalCoord_combination u x y r q hrq, hx, hy]
  simp

theorem sideCrease_convex {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s t : Side m) : Convex ℝ (sideCrease a u s t) :=
  (sideFace_convex a u s).inter (sideFace_convex a u t)

/-- The ambient point with the supplied native tangent and normal coordinates. -/
def keyCoordinatePoint  (u : Site C) (v : Fin m → ℝ) (z : ℝ) : Space m :=
  siteCenter u + (∑ i, v i • siteAxis u i) + z • outward u.1

@[simp] theorem keyCoordinatePoint_normal  (u : Site C)
    (v : Fin m → ℝ) (z : ℝ) : normalCoord u (keyCoordinatePoint u v z) = z := by
  have horth : ∀ i, ⟪outward u.1, siteAxis u i⟫_ℝ = 0 := by
    intro i
    rw [real_inner_comm]
    exact siteAxis_outward_inner u i
  have hsub : keyCoordinatePoint u v z - siteCenter u =
      (∑ i, v i • siteAxis u i) + z • outward u.1 := by
    unfold keyCoordinatePoint
    abel
  simp [normalCoord, hsub, inner_add_right, inner_sum,
    real_inner_smul_right, horth]

@[simp] theorem keyCoordinatePoint_tangent  (u : Site C)
    (v : Fin m → ℝ) (z : ℝ) (i : Fin m) :
    tangentCoord u (keyCoordinatePoint u v z) i = v i := by
  have hsub : keyCoordinatePoint u v z - siteCenter u =
      (∑ j, v j • siteAxis u j) + z • outward u.1 := by
    unfold keyCoordinatePoint
    abel
  simp [tangentCoord, hsub, inner_add_right, inner_sum,
    real_inner_smul_right, siteAxis_inner]

/-- The actual signed apex, valid for either sign of the nonzero coefficient. -/
def keyApex {J : ℕ} (a : Coefficients C J) (u : Site C) : Space m :=
  keyCoordinatePoint u (fun _ => 0) (eta m * (a.value u : ℝ) / denominator m J)

theorem keyApex_mem_sideFace {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s : Side m) : keyApex a u ∈ sideFace a u s := by
  have hp : ∀ t : Side m, branchProfile J u t (keyApex a u) = 1 := by
    intro t
    simp [keyApex, branchProfile]
  have hreg : keyApex a u ∈ branchRegion J u s := by
    exact ⟨by rw [hp]; norm_num, fun t => by rw [hp, hp]⟩
  have hheight : normalCoord u (keyApex a u) = siteHeight a u (keyApex a u) := by
    rw [siteHeight_eq_sideHeight a u s _ hreg]
    simp [sideHeight, keyApex]
  refine ⟨⟨⟨?_, ?_⟩, hheight⟩, hreg⟩
  · rw [hheight]
    exact (siteHeight_abs_lt_rho a u _).le
  · intro i
    simp only [keyApex, keyCoordinatePoint_tangent]
    exact ⟨div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (eta_pos m).le)
      (pMinus_pos J i).le, div_nonneg (eta_pos m).le (pPlus_pos J i).le⟩


/-- A selected signed endpoint of a native footprint interval. -/
def sideEndpoint  (J : ℕ) (s : Side m) : ℝ :=
  if s.2 then eta m / pPlus J s.1 else -eta m / pMinus J s.1

/-- An explicit footprint vertex on the chosen side. Other axes use their
negative endpoints, so every distinct axis supplies an incident side crease. -/
def keyBaseVertex  (J : ℕ) (u : Site C) (s : Side m) : Space m :=
  keyCoordinatePoint u
    (fun i => if i = s.1 then sideEndpoint J s else -eta m / pMinus J i) 0

theorem keyBaseVertex_mem_closedTube  (J : ℕ) (u : Site C)
    (s : Side m) : keyBaseVertex J u s ∈ closedTube J u := by
  refine ⟨?_, fun i => ?_⟩
  · simp only [keyBaseVertex, keyCoordinatePoint_normal, abs_zero]
    exact (rho_pos m).le
  · simp only [keyBaseVertex, keyCoordinatePoint_tangent]
    have hlo : -eta m / pMinus J i ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (eta_pos m).le) (pMinus_pos J i).le
    have hhi : 0 ≤ eta m / pPlus J i := div_nonneg (eta_pos m).le (pPlus_pos J i).le
    by_cases hi : i = s.1
    · subst i
      simp only [ite_true, sideEndpoint]
      split_ifs <;> exact ⟨by first | exact hlo.trans hhi | rfl,
        by first | exact hlo.trans hhi | rfl⟩
    · simp only [hi, ite_false]
      exact ⟨le_rfl, hlo.trans hhi⟩

theorem keyBaseVertex_branch_zero  (J : ℕ) (u : Site C)
    (s : Side m) : branchProfile J u s (keyBaseVertex J u s) = 0 := by
  rcases s with ⟨i, b⟩
  have he := (eta_pos m).ne'
  have hm := (pMinus_pos J i).ne'
  have hp := (pPlus_pos J i).ne'
  cases b
  · rw [branchProfile_false]
    simp only [keyBaseVertex, keyCoordinatePoint_tangent, ite_true, sideEndpoint,
      Bool.false_eq_true, ite_false]
    field_simp
    ring
  · rw [branchProfile_true]
    simp only [keyBaseVertex, keyCoordinatePoint_tangent, ite_true, sideEndpoint]
    field_simp
    ring

theorem keyBaseVertex_other_branch_zero  (J : ℕ) (u : Site C)
    (s : Side m) (j : Fin m) (hj : j ≠ s.1) :
    branchProfile J u (j, false) (keyBaseVertex J u s) = 0 := by
  rw [branchProfile_false]
  simp only [keyBaseVertex, keyCoordinatePoint_tangent, hj, ite_false]
  field_simp [(eta_pos m).ne', (pMinus_pos J j).ne']
  ring

/-- A zero active branch on the zero-height footprint is a literal base crease. -/
theorem mem_baseCrease_of_branch_zero {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s : Side m) (x : Space m) (hx : x ∈ closedTube J u)
    (hn : normalCoord u x = 0) (hp : branchProfile J u s x = 0) :
    x ∈ baseCrease a u s := by
  have hreg : x ∈ branchRegion J u s := by
    rw [branchRegion, mem_ofPred_eq, hp]
    exact ⟨le_rfl, fun t => branchProfile_nonneg_of_mem_closedTube J u t x hx⟩
  refine ⟨⟨⟨hx, ?_⟩, hreg⟩, hn⟩
  rw [hn]
  unfold siteHeight keyHeight
  rw [native_profile_eq_branch J u s x hreg, hp, mul_zero]

theorem keyBaseVertex_mem_baseCrease {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s : Side m) : keyBaseVertex J u s ∈ baseCrease a u s :=
  mem_baseCrease_of_branch_zero a u s _ (keyBaseVertex_mem_closedTube J u s)
    (by simp [keyBaseVertex]) (keyBaseVertex_branch_zero J u s)

theorem keyBaseVertex_mem_other_baseCrease {J : ℕ} [NeZero m]
    (a : Coefficients C J) (u : Site C) (s : Side m) (j : Fin m) (hj : j ≠ s.1) :
    keyBaseVertex J u s ∈ baseCrease a u (j, false) :=
  mem_baseCrease_of_branch_zero a u (j, false) _ (keyBaseVertex_mem_closedTube J u s)
    (by simp [keyBaseVertex]) (keyBaseVertex_other_branch_zero J u s j hj)

theorem baseCrease_nonempty {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s : Side m) : (baseCrease a u s).Nonempty :=
  ⟨keyBaseVertex J u s, keyBaseVertex_mem_baseCrease a u s⟩

theorem sideCrease_nonempty {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s t : Side m) : (sideCrease a u s t).Nonempty :=
  ⟨keyApex a u, keyApex_mem_sideFace a u s, keyApex_mem_sideFace a u t⟩

theorem baseCrease_isConnected {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s : Side m) : IsConnected (baseCrease a u s) :=
  (baseCrease_convex a u s).isConnected (baseCrease_nonempty a u s)

theorem sideCrease_isConnected {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s t : Side m) : IsConnected (sideCrease a u s t) :=
  (sideCrease_convex a u s t).isConnected (sideCrease_nonempty a u s t)

/-- Every base face meets a genuine distinct-axis side crease, at a concrete
footprint vertex. No graph-incidence premise is supplied. -/
theorem baseCrease_meets_sideCrease {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s : Side m) (j : Fin m) (hj : j ≠ s.1) :
    (baseCrease a u s ∩ sideCrease a u s (j, false)).Nonempty := by
  exact ⟨keyBaseVertex J u s, keyBaseVertex_mem_baseCrease a u s,
    (keyBaseVertex_mem_baseCrease a u s).1,
    (keyBaseVertex_mem_other_baseCrease a u s j hj).1⟩


theorem baseCrease_subset_creaseComplex {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s : Side m) : baseCrease a u s ⊆ creaseComplex a u := by
  intro x hx
  exact Or.inl (mem_iUnion.mpr ⟨s, hx⟩)

theorem sideCrease_subset_creaseComplex {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) (s t : Side m) (hst : s.1 ≠ t.1) :
    sideCrease a u s t ⊆ creaseComplex a u := by
  intro x hx
  exact Or.inr (mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨⟨t, hst⟩, hx⟩⟩)

theorem creaseComplex_nonempty {J : ℕ} [NeZero m] (a : Coefficients C J)
    (u : Site C) : (creaseComplex a u).Nonempty := by
  let s : Side m := (⟨0, NeZero.pos m⟩, false)
  exact (baseCrease_nonempty a u s).mono (baseCrease_subset_creaseComplex a u s)

private theorem exists_other_axis  (hm : 2 ≤ m) (i : Fin m) :
    ∃ j : Fin m, j ≠ i := by
  by_cases hi : i.val = 0
  · refine ⟨⟨1, by omega⟩, ?_⟩
    intro h
    have := congrArg Fin.val h
    simp [hi] at this
  · refine ⟨⟨0, by omega⟩, ?_⟩
    intro h
    apply hi
    exact (congrArg Fin.val h).symm

/-- All native closed crease pieces are connected through their computed
incidences: side creases contain the apex and base creases meet side creases. -/
theorem creaseComplex_isPreconnected {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients C J) (u : Site C) : IsPreconnected (creaseComplex a u) := by
  apply isPreconnected_of_forall (keyApex a u)
  intro y hy
  rcases hy with hy | hy
  · obtain ⟨s, hs⟩ := mem_iUnion.mp hy
    obtain ⟨j, hj⟩ := exists_other_axis hm s.1
    let t : Side m := (j, false)
    refine ⟨baseCrease a u s ∪ sideCrease a u s t, ?_, ?_, Or.inl hs, ?_⟩
    · exact union_subset (baseCrease_subset_creaseComplex a u s)
        (sideCrease_subset_creaseComplex a u s t (Ne.symm hj))
    · exact Or.inr ⟨keyApex_mem_sideFace a u s, keyApex_mem_sideFace a u t⟩
    · exact (baseCrease_isConnected a u s).isPreconnected.union'
        (baseCrease_meets_sideCrease a u s j hj)
        (sideCrease_isConnected a u s t).isPreconnected
  · obtain ⟨s, hs⟩ := mem_iUnion.mp hy
    obtain ⟨t, ht⟩ := mem_iUnion.mp hs
    exact ⟨sideCrease a u s t.val,
      sideCrease_subset_creaseComplex a u s t.val t.property,
      ⟨keyApex_mem_sideFace a u s, keyApex_mem_sideFace a u t.val⟩,
      ht, (sideCrease_isConnected a u s t.val).isPreconnected⟩

/-- The actual native key crease complex is nonempty and connected in every
ambient dimension at least three, with no connectivity or incidence hypothesis. -/
theorem creaseComplex_isConnected {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients C J) (u : Site C) : IsConnected (creaseComplex a u) :=
  ⟨creaseComplex_nonempty a u, creaseComplex_isPreconnected hm a u⟩


/-- The native tangent frame together with the outward normal determines every
ambient point; no ambient coordinate is lost by passing to the key chart. -/
theorem eq_of_key_coordinates  (u : Site C) (x y : Space m)
    (hn : normalCoord u x = normalCoord u y)
    (ht : ∀ i, tangentCoord u x i = tangentCoord u y i) : x = y := by
  ext k
  by_cases hk : k = normalIndex u.1
  · subst k
    have hnonzero : normalSign u.1 ≠ 0 := by
      intro h
      have ha := abs_normalSign u.1
      simp [h] at ha
    simp only [normalCoord, outward_inner_coordinate, PiLp.sub_apply] at hn
    have := mul_left_cancel₀ hnonzero hn
    linarith
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hk
    let i := u.2.1.symm j
    have hi : u.2.1 i = j := u.2.1.apply_symm_apply j
    have hnonzero : sign (u.2.2 i) ≠ 0 := by
      intro h
      have ha := abs_sign (u.2.2 i)
      simp [h] at ha
    have h := ht i
    simp only [tangentCoord, siteAxis_inner_coordinate, hi, hj, PiLp.sub_apply] at h
    have := mul_left_cancel₀ hnonzero h
    linarith

/-- Opposite sides on one tangent axis intersect only at the apex. This is the
exceptional, lower-dimensional incidence omitted from the distinct-axis class. -/
theorem opposite_sideCrease_eq_singleton {J : ℕ} [NeZero m]
    (a : Coefficients C J) (u : Site C) (i : Fin m) :
    sideCrease a u (i, false) (i, true) = {keyApex a u} := by
  ext x
  constructor
  · intro hx
    have he := eta_pos m
    have heq : branchProfile J u (i, false) x = branchProfile J u (i, true) x :=
      le_antisymm (hx.1.2.2 (i, true)) (hx.2.2.2 (i, false))
    rw [branchProfile_false, branchProfile_true] at heq
    have hprod : (pMinus J i + pPlus J i) * tangentCoord u x i = 0 := by
      field_simp [he.ne'] at heq
      nlinarith [heq]
    have hi : tangentCoord u x i = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (add_pos (pMinus_pos J i) (pPlus_pos J i)).ne'
    have ht : ∀ j, tangentCoord u x j = 0 := by
      intro j
      have hlo := hx.1.2.2 (j, false)
      have hhi := hx.1.2.2 (j, true)
      rw [branchProfile_false, branchProfile_false, hi] at hlo
      rw [branchProfile_false, branchProfile_true, hi] at hhi
      simp only [mul_zero, zero_div, add_zero] at hlo hhi
      have hlo' : 0 ≤ pMinus J j * tangentCoord u x j := by
        have hd : 0 ≤ pMinus J j * tangentCoord u x j / eta m := by linarith
        have h := (le_div_iff₀ he).mp hd
        simpa using h
      have hhi' : pPlus J j * tangentCoord u x j ≤ 0 := by
        have hd : pPlus J j * tangentCoord u x j / eta m ≤ 0 := by linarith
        have h := (div_le_iff₀ he).mp hd
        simpa using h
      apply le_antisymm
      · by_contra hj
        have h := mul_pos (pPlus_pos J j) (lt_of_not_ge hj)
        linarith
      · exact (mul_nonneg_iff_of_pos_left (pMinus_pos J j)).mp hlo'
    apply mem_singleton_iff.mpr
    apply eq_of_key_coordinates u x (keyApex a u)
    · rw [hx.1.1.2, siteHeight_eq_sideHeight a u (i, false) x hx.1.2]
      simp [sideHeight, ht, keyApex]
    · intro j
      simp [ht, keyApex]
  · rintro rfl
    exact ⟨keyApex_mem_sideFace a u (i, false), keyApex_mem_sideFace a u (i, true)⟩


end
end ProductClosure.NativeCompiler
