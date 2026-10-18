module

public import ProductClosure.CreaseNormalSpan
public import ProductClosure.KeyNormalRank
public import ProductClosure.PlacedConicalGerms

@[expose] public section

/-! Recovering carrier-normal and tangent-axis lines from labelled base
creases. The argument uses actual affine-plane containment and explicit
native orthogonal coordinates, without a polytope facet-count certificate. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

@[simp] theorem placedNormal_inner_map_map  (f : Space m ≃ᵢ Space m)
    (v w : Space m) : ⟪placedNormal f v, placedNormal f w⟫_ℝ = ⟪v, w⟫_ℝ :=
  f.toRealAffineIsometryEquiv.linearIsometryEquiv.inner_map_map v w

/-- The intersection of two distinct-axis base normal planes is exactly the
carrier-normal line, proved using the literal nonzero signed slopes. -/
theorem placed_base_spans_intersection {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (f : Space m ≃ᵢ Space m) (s t : Side m) (hst : s.1 ≠ t.1)
    (n : Space m)
    (hs : n ∈ Submodule.span ℝ {placedNormal f (outward u.1), placedNormal f (sideNormal a u s)})
    (ht : n ∈ Submodule.span ℝ {placedNormal f (outward u.1), placedNormal f (sideNormal a u t)}) :
    ∃ c : ℝ, n = c • placedNormal f (outward u.1) := by
  obtain ⟨c, d, hs⟩ := Submodule.mem_span_pair.mp hs
  obtain ⟨e, k, ht⟩ := Submodule.mem_span_pair.mp ht
  have hh := congrArg (fun z : Space m => ⟪z, placedNormal f (siteAxis u s.1)⟫_ℝ)
    (hs.trans ht.symm)
  have ho : ⟪outward u.1, siteAxis u s.1⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact siteAxis_outward_inner u s.1
  simp only [inner_add_left, real_inner_smul_left, placedNormal_inner_map_map,
    ho, sideNormal_inner_siteAxis, hst.symm, ↓reduceIte, mul_zero, zero_add] at hh
  have hd : d = 0 := (mul_eq_zero.mp hh).resolve_right (neg_ne_zero.mpr (sideSlope_ne_zero a u s))
  exact ⟨c, by simpa [hd] using hs.symm⟩

/-- Any plane containing all labelled base creases has normal parallel to
the actual carrier normal. Two tangent axes suffice; m>=2 supplies them. -/
theorem placed_all_base_containing_normal {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u : Site polyCells) (f : Space m ≃ᵢ Space m)
    (n : Space m) (c : ℝ)
    (hcontain : ∀ s : Side m, ∀ y ∈ f '' baseCrease a u s, ⟪n, y⟫_ℝ = c) :
    ∃ r : ℝ, n = r • placedNormal f (outward u.1) := by
  let s : Side m := (⟨0, by omega⟩, false)
  let t : Side m := (⟨1, by omega⟩, false)
  exact placed_base_spans_intersection a u f s t (by simp [s, t]) n
    (placed_baseCrease_containing_normal_mem_span a u s f n c (hcontain s))
    (placed_baseCrease_containing_normal_mem_span a u t f n c (hcontain t))

/-- Every placed base crease lies in the actual placed carrier plane. -/
theorem placed_baseCrease_outward_plane {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m)
    (f : Space m ≃ᵢ Space m) (y : Space m) (hy : y ∈ f '' baseCrease a u s) :
    ⟪placedNormal f (outward u.1), y⟫_ℝ =
      ⟪placedNormal f (outward u.1), f (siteCenter u)⟫_ℝ := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hzero : ⟪placedNormal f (outward u.1), f z - f (siteCenter u)⟫_ℝ = 0 := by
    rw [placedNormal_inner_sub]
    simpa [normalCoord] using hz.2
  rw [inner_sub_right] at hzero
  linarith

/-- Equality of all labelled actual base creases recovers the carrier-normal
line under completely unrestricted ambient placements. -/
theorem labelled_baseCreases_outward_eq_or_neg {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (u v : Site polyCells) (f g : Space m ≃ᵢ Space m)
    (hbase : ∀ s : Side m, f '' baseCrease a u s = g '' baseCrease a v s) :
    placedNormal g (outward v.1) = placedNormal f (outward u.1) ∨
      placedNormal g (outward v.1) = -placedNormal f (outward u.1) := by
  obtain ⟨r, hr⟩ := placed_all_base_containing_normal hm a u f
    (placedNormal g (outward v.1))
    ⟪placedNormal g (outward v.1), g (siteCenter v)⟫_ℝ
    (fun s y hy => placed_baseCrease_outward_plane a v s g y ((hbase s) ▸ hy))
  have hn := congrArg norm hr
  have habs : |r| = 1 := by simpa [placedNormal, norm_smul, Real.norm_eq_abs] using hn.symm
  by_cases hsign : 0 ≤ r
  · have hpos : r = 1 := by simpa [abs_of_nonneg hsign] using habs
    left; simpa [hpos] using hr
  · have hneg : r = -1 := by rw [abs_of_neg (lt_of_not_ge hsign)] at habs; linarith
    right; simpa [hneg] using hr

end
end ProductClosure.NativeCompiler
