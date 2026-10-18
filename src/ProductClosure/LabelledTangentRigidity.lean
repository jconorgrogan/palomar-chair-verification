module

public import ProductClosure.BasePlaneRigidity

@[expose] public section

/-! Exact recovery of tangent orientations and site centers from every
corresponding full-labelled base crease under arbitrary ambient isometries. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- A full base label fixes its actual tangent endpoint. -/
theorem baseCrease_tangentCoord_eq_endpoint {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m) (x : Space m)
    (hx : x ∈ baseCrease a u s) : tangentCoord u x s.1 = sideEndpoint J s := by
  have h := baseCrease_branch_zero a u s x hx
  rcases s with ⟨i, b⟩
  cases b
  · rw [branchProfile_false] at h
    simp only [sideEndpoint, Bool.false_eq_true, ↓reduceIte]
    apply (eq_div_iff (pMinus_pos J i).ne').mpr
    have hh : pMinus J i * tangentCoord u x i = -eta m := by
      have he : pMinus J i * tangentCoord u x i / eta m = -1 := by linarith
      simpa using (div_eq_iff (eta_pos m).ne').mp he
    nlinarith
  · rw [branchProfile_true] at h
    simp only [sideEndpoint, ↓reduceIte]
    apply (eq_div_iff (pPlus_pos J i).ne').mpr
    have hh : pPlus J i * tangentCoord u x i = eta m := by
      have he : pPlus J i * tangentCoord u x i / eta m = 1 := by linarith
      simpa using (div_eq_iff (eta_pos m).ne').mp he
    nlinarith

/-- The exact tangent endpoint equation survives an unrestricted placement. -/
theorem placed_baseCrease_tangent_plane {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m)
    (f : Space m ≃ᵢ Space m) (y : Space m) (hy : y ∈ f '' baseCrease a u s) :
    ⟪placedNormal f (siteAxis u s.1), y - f (siteCenter u)⟫_ℝ =
      sideEndpoint J s := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [placedNormal_inner_sub]
  simpa [tangentCoord] using baseCrease_tangentCoord_eq_endpoint a u s x hx

/-- A companion tangent axis lies on the corresponding root tangent line. -/
theorem labelled_baseCreases_axis_parallel {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u v : Site polyCells) (f g : Space m ≃ᵢ Space m)
    (hbase : ∀ s : Side m, f '' baseCrease a u s = g '' baseCrease a v s)
    (i : Fin m) :
    ∃ r : ℝ, placedNormal g (siteAxis v i) = r • placedNormal f (siteAxis u i) := by
  let s : Side m := (i, false)
  have hmem : placedNormal g (siteAxis v i) ∈ Submodule.span ℝ
      {placedNormal f (outward u.1), placedNormal f (sideNormal a u s)} := by
    apply placed_baseCrease_containing_normal_mem_span a u s f _
      (sideEndpoint J s + ⟪placedNormal g (siteAxis v i), g (siteCenter v)⟫_ℝ)
    intro y hy
    have h := placed_baseCrease_tangent_plane a v s g y ((hbase s) ▸ hy)
    rw [inner_sub_right] at h
    linarith
  have horth : ⟪placedNormal g (siteAxis v i), placedNormal f (outward u.1)⟫_ℝ = 0 := by
    have h := siteAxis_outward_inner v i
    rcases labelled_baseCreases_outward_eq_or_neg hm a u v f g hbase with hn | hn
    · rw [← hn, placedNormal_inner_map_map]; exact h
    · have hh := placedNormal_inner_map_map g (siteAxis v i) (outward v.1)
      rw [hn, inner_neg_right, h] at hh
      linarith
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hmem
  have hn := congrArg (fun z : Space m => ⟪z, placedNormal f (outward u.1)⟫_ℝ) hcd
  simp only [inner_add_left, real_inner_smul_left, placedNormal_inner_map_map,
    sideNormal_inner_outward, mul_one, horth] at hn
  have hunit : ⟪outward u.1, outward u.1⟫_ℝ = 1 := by simp
  rw [hunit, mul_one] at hn
  have hc : c = -d := by linarith
  refine ⟨-d * sideSlope a u s, ?_⟩
  rw [← hcd, hc]
  simp only [sideNormal, placedNormal, map_sub, map_smul, smul_sub, smul_smul]
  change (-d) • _ + (d • _ - (d * sideSlope a u s) • _) = _
  rw [neg_smul, neg_mul, neg_smul]
  abel

/-- Labelled lower and upper endpoints have strictly positive separation. -/
theorem sideEndpoint_gap_pos  (J : ℕ) (i : Fin m) :
    0 < sideEndpoint J (i, true) - sideEndpoint J (i, false) := by
  simp only [sideEndpoint, ↓reduceIte, Bool.false_eq_true]
  have hp := div_pos (eta_pos m) (pPlus_pos J i)
  have hm := div_neg_of_neg_of_pos (neg_neg_of_pos (eta_pos m)) (pMinus_pos J i)
  linarith

/-- Matching both signed labels removes every tangent-axis sign ambiguity. -/
theorem labelled_baseCreases_tangent_eq {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u v : Site polyCells) (f g : Space m ≃ᵢ Space m)
    (hbase : ∀ s : Side m, f '' baseCrease a u s = g '' baseCrease a v s)
    (i : Fin m) : placedNormal g (siteAxis v i) = placedNormal f (siteAxis u i) := by
  obtain ⟨r, hr⟩ := labelled_baseCreases_axis_parallel hm a u v f g hbase i
  have he (b : Bool) :
      r * (sideEndpoint J (i, b) +
        ⟪placedNormal f (siteAxis u i), f (siteCenter u)⟫_ℝ -
        ⟪placedNormal f (siteAxis u i), g (siteCenter v)⟫_ℝ) =
      sideEndpoint J (i, b) := by
    let x := keyBaseVertex J u (i, b)
    have hx : f x ∈ f '' baseCrease a u (i, b) :=
      ⟨x, keyBaseVertex_mem_baseCrease a u (i, b), rfl⟩
    have hu := placed_baseCrease_tangent_plane a u (i, b) f (f x) hx
    have hv := placed_baseCrease_tangent_plane a v (i, b) g (f x) ((hbase (i, b)) ▸ hx)
    rw [hr, real_inner_smul_left, inner_sub_right] at hv
    rw [inner_sub_right] at hu
    have huu : ⟪placedNormal f (siteAxis u i), f x⟫_ℝ =
        sideEndpoint J (i, b) + ⟪placedNormal f (siteAxis u i), f (siteCenter u)⟫_ℝ := by
      linarith
    rwa [huu] at hv
  have hgap := sideEndpoint_gap_pos J i
  have hfalse := he false
  have htrue := he true
  have hrone : r = 1 := by nlinarith
  simpa [hrone] using hr

/-- All placed key-frame inner products determine the world point. -/
theorem placed_key_coordinates_ext  (u : Site polyCells)
    (f : Space m ≃ᵢ Space m) (x y : Space m)
    (hn : ⟪placedNormal f (outward u.1), x⟫_ℝ =
      ⟪placedNormal f (outward u.1), y⟫_ℝ)
    (ht : ∀ i, ⟪placedNormal f (siteAxis u i), x⟫_ℝ =
      ⟪placedNormal f (siteAxis u i), y⟫_ℝ) : x = y := by
  apply f.symm.injective
  apply eq_of_key_coordinates u
  · have hz : ⟪outward u.1, f.symm x - f.symm y⟫_ℝ = 0 := by
      rw [← placedNormal_inner_sub, inner_sub_right, hn, sub_self]
    simp only [normalCoord, inner_sub_right] at hz ⊢
    linarith
  · intro i
    have hz : ⟪siteAxis u i, f.symm x - f.symm y⟫_ℝ = 0 := by
      rw [← placedNormal_inner_sub, inner_sub_right, ht i, sub_self]
    simp only [tangentCoord, inner_sub_right] at hz ⊢
    linarith

/-- Equality of all fully labelled actual base creases identifies their site
centers, even though the two outward normals may have opposite signs. -/
theorem labelled_baseCreases_center_eq {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u v : Site polyCells) (f g : Space m ≃ᵢ Space m)
    (hbase : ∀ s : Side m, f '' baseCrease a u s = g '' baseCrease a v s) :
    f (siteCenter u) = g (siteCenter v) := by
  apply placed_key_coordinates_ext u f
  · let s : Side m := (⟨0, by omega⟩, false)
    let x := f (keyBaseVertex J u s)
    have hx : x ∈ f '' baseCrease a u s :=
      ⟨keyBaseVertex J u s, keyBaseVertex_mem_baseCrease a u s, rfl⟩
    have hu := placed_baseCrease_outward_plane a u s f x hx
    have hv := placed_baseCrease_outward_plane a v s g x ((hbase s) ▸ hx)
    rcases labelled_baseCreases_outward_eq_or_neg hm a u v f g hbase with hn | hn
    · rw [hn] at hv
      exact hu.symm.trans hv
    · rw [hn, inner_neg_left, inner_neg_left] at hv
      linarith
  · intro i
    let s : Side m := (i, false)
    let x := f (keyBaseVertex J u s)
    have hx : x ∈ f '' baseCrease a u s :=
      ⟨keyBaseVertex J u s, keyBaseVertex_mem_baseCrease a u s, rfl⟩
    have hu := placed_baseCrease_tangent_plane a u s f x hx
    have hv := placed_baseCrease_tangent_plane a v s g x ((hbase s) ▸ hx)
    have hi := labelled_baseCreases_tangent_eq hm a u v f g hbase i
    change ⟪placedNormal g (siteAxis v i), x - g (siteCenter v)⟫_ℝ = _ at hv
    rw [hi, inner_sub_right] at hv
    rw [inner_sub_right] at hu
    linarith

/-- Full base-label matching recovers the center and every oriented tangent
axis from actual crease equality alone. -/
theorem labelled_baseCreases_frame_center {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u v : Site polyCells) (f g : Space m ≃ᵢ Space m)
    (hbase : ∀ s : Side m, f '' baseCrease a u s = g '' baseCrease a v s) :
    (∀ i, placedNormal g (siteAxis v i) = placedNormal f (siteAxis u i)) ∧
      f (siteCenter u) = g (siteCenter v) :=
  ⟨labelled_baseCreases_tangent_eq hm a u v f g hbase,
    labelled_baseCreases_center_eq hm a u v f g hbase⟩


end
end ProductClosure.NativeCompiler
