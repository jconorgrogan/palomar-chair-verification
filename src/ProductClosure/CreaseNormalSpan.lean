module

public import PhysicalRegistration.CreaseNormalSpan
public import ProductClosure.CreasePlaneGerms

@[expose] public section
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration
open scoped InnerProductSpace Topology
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- Every affine plane containing the actual native base crease has its normal
in the span of the actual outward and side normals. -/
theorem baseCrease_containing_normal_mem_span {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m) (n : Space m) (c : ℝ)
    (hcontain : ∀ y ∈ baseCrease a u s, ⟪n, y⟫_ℝ = c) :
    n ∈ Submodule.span ℝ {outward u.1, sideNormal a u s} := by
  obtain ⟨x, hx⟩ := genericBaseCrease_nonempty a u s
  obtain ⟨U, hU, hxU, hgerm⟩ :=
    genericBaseCrease_locally_eq_plane_intersection a u s x hx
  exact normal_mem_span_pair_of_local_plane_intersection
    (baseCrease a u s) U x (siteCenter u) (outward u.1) (sideNormal a u s) n
    0 (eta m * (a.value u : ℝ) / denominator m J) c hU hxU hx.1 hgerm hcontain

/-- Every affine plane containing the actual native distinct-axis side crease
has its normal in the span of the two actual side normals. -/
theorem sideCrease_containing_normal_mem_span {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1)
    (n : Space m) (c : ℝ)
    (hcontain : ∀ y ∈ sideCrease a u s t, ⟪n, y⟫_ℝ = c) :
    n ∈ Submodule.span ℝ {sideNormal a u s, sideNormal a u t} := by
  obtain ⟨x, hx⟩ := genericSideCrease_nonempty a u s t hst
  obtain ⟨U, hU, hxU, hgerm⟩ :=
    genericSideCrease_locally_eq_plane_intersection a u s t x hx
  exact normal_mem_span_pair_of_local_plane_intersection
    (sideCrease a u s t) U x (siteCenter u) (sideNormal a u s) (sideNormal a u t) n
    (eta m * (a.value u : ℝ) / denominator m J)
    (eta m * (a.value u : ℝ) / denominator m J) c hU hxU hx.1 hgerm hcontain

/-- The base-crease normal-span conclusion for an arbitrary ambient placement. -/
theorem placed_baseCrease_containing_normal_mem_span {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m)
    (f : Space m ≃ᵢ Space m) (n : Space m) (c : ℝ)
    (hcontain : ∀ y ∈ f '' baseCrease a u s, ⟪n, y⟫_ℝ = c) :
    n ∈ Submodule.span ℝ
      {placedNormal f (outward u.1), placedNormal f (sideNormal a u s)} := by
  exact normal_mem_span_pair_of_image_containment (baseCrease a u s)
    (outward u.1) (sideNormal a u s) f n c
    (fun n' c' h => baseCrease_containing_normal_mem_span a u s n' c' h) hcontain

/-- The distinct-axis side-crease normal-span conclusion for an arbitrary
ambient placement, with no restriction on its orthogonal linear part. -/
theorem placed_sideCrease_containing_normal_mem_span {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1)
    (f : Space m ≃ᵢ Space m) (n : Space m) (c : ℝ)
    (hcontain : ∀ y ∈ f '' sideCrease a u s t, ⟪n, y⟫_ℝ = c) :
    n ∈ Submodule.span ℝ
      {placedNormal f (sideNormal a u s), placedNormal f (sideNormal a u t)} := by
  exact normal_mem_span_pair_of_image_containment (sideCrease a u s t)
    (sideNormal a u s) (sideNormal a u t) f n c
    (fun n' c' h => sideCrease_containing_normal_mem_span a u s t hst n' c' h) hcontain


end
end ProductClosure.NativeCompiler
