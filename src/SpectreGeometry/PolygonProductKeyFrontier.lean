module

public import SpectreGeometry.PolygonProductKeyBody

@[expose] public section


/-! Actual frontier membership for the literal optimized P×P keyed body.

The local membership equivalence on each collar interior, rather than merely
the one-sided `LocalLipschitzGraphAt` interface, identifies the body's interior
and frontier there. Positive shifts in the unit outward normal leave the body;
negative shifts enter its interior. The global normal-shift invariance of the
literal height supplies both statements. No additional geometric assumptions,
whole-feature matching assumptions, or global tiling conclusions are used.
-/

namespace PhysicalRegistration
open Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The signed hypograph gap increases by exactly the normal displacement. -/
theorem centeredHypograph_normal_shift_gap
    (center n : E) (hn : ‖n‖ = 1) (H : E → ℝ)
    (hshift : ∀ (v : E) (t : ℝ), H (v + t • n) = H v)
    (x : E) (t : ℝ) :
    inner ℝ n (x + t • n - center) - H (x + t • n - center) =
      (inner ℝ n (x - center) - H (x - center)) + t := by
  have hid : x + t • n - center = (x - center) + t • n := by abel
  rw [hid, inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hn, hshift]
  ring

/-- A strict local hypograph inequality gives an actual interior point of the
set that agrees with the hypograph on the specified open neighborhood. -/
theorem centeredHypograph_local_strict_mem_interior
    (S U : Set E) (hU : IsOpen U)
    (center n : E) (hn : ‖n‖ = 1) (H : E → ℝ) (hH : Continuous H)
    (hlocal : ∀ y ∈ U, y ∈ S ↔ inner ℝ n (y - center) ≤ H (y - center))
    (x : E) (hxU : x ∈ U)
    (hx : inner ℝ n (x - center) < H (x - center)) :
    x ∈ interior S := by
  have hopen : IsOpen {y : E | inner ℝ n (y - center) < H (y - center)} :=
    isOpen_lt
      ((unit_inner_continuous n hn).comp (continuous_id.sub continuous_const))
      (hH.comp (continuous_id.sub continuous_const))
  have hsubset : U ∩ {y : E | inner ℝ n (y - center) < H (y - center)} ⊆ S := by
    intro y hy
    exact (hlocal y hy.1).mpr hy.2.le
  exact interior_maximal hsubset (hU.inter hopen) ⟨hxU, hx⟩

/-- Every local graph point has arbitrarily close points outside the actual
set, so the graph point cannot belong to its interior. -/
theorem centeredHypograph_local_graph_not_mem_interior
    (S U : Set E) (hU : IsOpen U)
    (center n : E) (hn : ‖n‖ = 1) (H : E → ℝ)
    (hshift : ∀ (v : E) (t : ℝ), H (v + t • n) = H v)
    (hlocal : ∀ y ∈ U, y ∈ S ↔ inner ℝ n (y - center) ≤ H (y - center))
    (x : E) (hxU : x ∈ U)
    (hx : inner ℝ n (x - center) = H (x - center)) :
    x ∉ interior S := by
  intro hxI
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_interior.inter hU) x ⟨hxI, hxU⟩
  have ht : 0 < r / 2 := by linarith
  have hdist : dist (x + (r / 2) • n) x = r / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht, hn, mul_one]
  have hy : x + (r / 2) • n ∈ interior S ∩ U := by
    apply hball
    rw [Metric.mem_ball, hdist]
    linarith
  have hle := (hlocal (x + (r / 2) • n) hy.2).mp (interior_subset hy.1)
  have hgap := centeredHypograph_normal_shift_gap center n hn H hshift x (r / 2)
  rw [hx, sub_self, zero_add] at hgap
  linarith

/-- Exact interior classification wherever the actual set agrees locally with
a continuous, normal-shift-invariant hypograph. -/
theorem centeredHypograph_local_interior_iff
    (S U : Set E) (hU : IsOpen U)
    (center n : E) (hn : ‖n‖ = 1) (H : E → ℝ) (hH : Continuous H)
    (hshift : ∀ (v : E) (t : ℝ), H (v + t • n) = H v)
    (hlocal : ∀ y ∈ U, y ∈ S ↔ inner ℝ n (y - center) ≤ H (y - center))
    (x : E) (hxU : x ∈ U) :
    x ∈ interior S ↔ inner ℝ n (x - center) < H (x - center) := by
  constructor
  · intro hxI
    have hle := (hlocal x hxU).mp (interior_subset hxI)
    apply lt_of_le_of_ne hle
    intro heq
    exact centeredHypograph_local_graph_not_mem_interior S U hU center n hn H
      hshift hlocal x hxU heq hxI
  · exact centeredHypograph_local_strict_mem_interior S U hU center n hn H hH
      hlocal x hxU

/-- Closedness supplies the closure side of the frontier condition; the exact
local interior classification supplies its other side. -/
theorem centeredHypograph_local_frontier_iff
    (S U : Set E) (hS : IsClosed S) (hU : IsOpen U)
    (center n : E) (hn : ‖n‖ = 1) (H : E → ℝ) (hH : Continuous H)
    (hshift : ∀ (v : E) (t : ℝ), H (v + t • n) = H v)
    (hlocal : ∀ y ∈ U, y ∈ S ↔ inner ℝ n (y - center) ≤ H (y - center))
    (x : E) (hxU : x ∈ U) :
    x ∈ frontier S ↔ inner ℝ n (x - center) = H (x - center) := by
  rw [frontier, hS.closure_eq]
  change (x ∈ S ∧ x ∉ interior S) ↔
    inner ℝ n (x - center) = H (x - center)
  rw [hlocal x hxU,
    centeredHypograph_local_interior_iff S U hU center n hn H hH hshift hlocal x hxU]
  constructor
  · intro hx
    exact le_antisymm hx.1 (le_of_not_gt hx.2)
  · intro hx
    exact ⟨hx.le, not_lt_of_ge hx.ge⟩

/-- Both sides of every graph point are realized on a whole small normal
segment: positive normal shifts are outside, negative shifts are interior. -/
theorem centeredHypograph_local_normal_perturbations
    (S U : Set E) (hU : IsOpen U)
    (center n : E) (hn : ‖n‖ = 1) (H : E → ℝ) (hH : Continuous H)
    (hshift : ∀ (v : E) (t : ℝ), H (v + t • n) = H v)
    (hlocal : ∀ y ∈ U, y ∈ S ↔ inner ℝ n (y - center) ≤ H (y - center))
    (x : E) (hxU : x ∈ U)
    (hx : inner ℝ n (x - center) = H (x - center)) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      (x + t • n ∈ U ∧ x + t • n ∉ S) ∧
      (x + (-t) • n ∈ U ∧ x + (-t) • n ∈ interior S) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have hplusU : x + t • n ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, hn, mul_one]
    exact htδ
  have hminusU : x + (-t) • n ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_neg, abs_of_pos ht, hn, mul_one]
    exact htδ
  have hplus := centeredHypograph_normal_shift_gap center n hn H hshift x t
  have hminus := centeredHypograph_normal_shift_gap center n hn H hshift x (-t)
  rw [hx, sub_self, zero_add] at hplus hminus
  refine ⟨⟨hplusU, ?_⟩, ⟨hminusU, ?_⟩⟩
  · intro hyS
    have hy := (hlocal (x + t • n) hplusU).mp hyS
    linarith
  · apply centeredHypograph_local_strict_mem_interior S U hU center n hn H hH
      hlocal (x + (-t) • n) hminusU
    linarith

end PhysicalRegistration

namespace SpectreGeometry
noncomputable section
open Set PhysicalRegistration
open scoped InnerProductSpace

theorem product_key_height_continuous (s : ProductKeySite) :
    Continuous (productKeyHeight s) := by
  have hH : LipschitzWith ⟨34 / 4357, product_key_slope_below_half.1⟩
      (productKeyHeight s) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    change dist (productKeyHeight s v) (productKeyHeight s w) ≤
      (34 / 4357 : ℝ) * dist v w
    simpa only [dist_eq_norm, Real.norm_eq_abs] using product_key_height_lipschitz s v w
  exact hH.continuous

/-- Within each actual collar interior, strict inequality is exactly interior
membership in the literal assembled body. -/
theorem polygon_product_key_body_interior_local_iff
    (s : ProductKeySite) (x : EFour) (hx : x ∈ interior (productKeyCollar s)) :
    x ∈ interior polygonProductKeyBody ↔
      inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s) <
        productKeyHeight s (x - productKeyCenter s) :=
  centeredHypograph_local_interior_iff polygonProductKeyBody
    (interior (productKeyCollar s)) isOpen_interior
    (productKeyCenter s) (productKeyOutwardNormal s) (productKeyOutwardNormal_norm s)
    (productKeyHeight s) (product_key_height_continuous s)
    (product_key_height_normal_shift s) (polygon_product_key_body_local_outward_iff s) x hx

/-- The literal body's frontier inside a collar is exactly the actual key
graph, including its creases, apex, and zero extension. -/
theorem polygon_product_key_body_frontier_local_iff
    (s : ProductKeySite) (x : EFour) (hx : x ∈ interior (productKeyCollar s)) :
    x ∈ frontier polygonProductKeyBody ↔ x ∈ productKeyGraph s :=
  centeredHypograph_local_frontier_iff polygonProductKeyBody
    (interior (productKeyCollar s)) polygon_product_key_body_isClosed isOpen_interior
    (productKeyCenter s) (productKeyOutwardNormal s) (productKeyOutwardNormal_norm s)
    (productKeyHeight s) (product_key_height_continuous s)
    (product_key_height_normal_shift s) (polygon_product_key_body_local_outward_iff s) x hx

theorem polygon_product_key_body_frontier_inter_collar_interior (s : ProductKeySite) :
    frontier polygonProductKeyBody ∩ interior (productKeyCollar s) =
      productKeyGraph s ∩ interior (productKeyCollar s) := by
  ext x
  constructor
  · intro hx
    exact ⟨(polygon_product_key_body_frontier_local_iff s x hx.2).mp hx.1, hx.2⟩
  · intro hx
    exact ⟨(polygon_product_key_body_frontier_local_iff s x hx.2).mpr hx.1, hx.2⟩

/-- Every point of every literal product-key graph window is an actual frontier
point of the bounded polygon-product keyed body. -/
theorem product_key_graph_window_subset_frontier (s : ProductKeySite) :
    productKeyGraphWindow s ⊆ frontier polygonProductKeyBody := by
  intro x hx
  exact (polygon_product_key_body_frontier_local_iff s x
    (product_key_graph_window_subset_interior_collar s hx)).mpr hx.1

theorem product_key_active_graph_mem_frontier
    (s : ProductKeySite) (x : EFour) (hx : x ∈ productKeyGraph s)
    (hactive : productKeyHeight s (x - productKeyCenter s) ≠ 0) :
    x ∈ frontier polygonProductKeyBody :=
  product_key_graph_window_subset_frontier s (product_key_active_graph_mem_window s x hx hactive)

/-- A direct two-sided boundary witness for each concrete graph-window point.
The normal directions here are the actual globally defined recipe normals. -/
theorem product_key_graph_window_normal_perturbations
    (s : ProductKeySite) (x : EFour) (hx : x ∈ productKeyGraphWindow s) :
    ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      (x + t • productKeyOutwardNormal s ∈ interior (productKeyCollar s) ∧
        x + t • productKeyOutwardNormal s ∉ polygonProductKeyBody) ∧
      (x + (-t) • productKeyOutwardNormal s ∈ interior (productKeyCollar s) ∧
        x + (-t) • productKeyOutwardNormal s ∈ interior polygonProductKeyBody) :=
  centeredHypograph_local_normal_perturbations polygonProductKeyBody
    (interior (productKeyCollar s)) isOpen_interior
    (productKeyCenter s) (productKeyOutwardNormal s) (productKeyOutwardNormal_norm s)
    (productKeyHeight s) (product_key_height_continuous s)
    (product_key_height_normal_shift s) (polygon_product_key_body_local_outward_iff s) x
    (product_key_graph_window_subset_interior_collar s hx) hx.1

/-- The concrete graph apex lies directly above or below its recipe center,
according to the sign of the key label. -/
def productKeyApex (s : ProductKeySite) : EFour :=
  productKeyCenter s + productKeyHeight s 0 • productKeyOutwardNormal s

theorem product_key_apex_mem_graph_window (s : ProductKeySite) :
    productKeyApex s ∈ productKeyGraphWindow s := by
  constructor
  · change inner ℝ (productKeyOutwardNormal s)
        (productKeyCenter s + productKeyHeight s 0 • productKeyOutwardNormal s -
          productKeyCenter s) =
      productKeyHeight s
        (productKeyCenter s + productKeyHeight s 0 • productKeyOutwardNormal s -
          productKeyCenter s)
    rw [add_sub_cancel_left]
    have hheight := product_key_height_normal_shift s 0 (productKeyHeight s 0)
    simp only [zero_add] at hheight
    rw [hheight, real_inner_smul_right, real_inner_self_eq_norm_sq,
      productKeyOutwardNormal_norm]
    ring
  · intro j
    change |inner ℝ (productKeyTangent s j)
      (productKeyCenter s + productKeyHeight s 0 • productKeyOutwardNormal s -
        productKeyCenter s)| ≤ productKeyEta
    have horth : inner ℝ (productKeyTangent s j) (productKeyOutwardNormal s) = 0 := by
      rw [real_inner_comm]
      exact productKeyOutwardNormal_inner_tangent s j
    rw [add_sub_cancel_left, real_inner_smul_right, horth]
    norm_num [productKeyEta]

theorem product_key_apex_mem_frontier (s : ProductKeySite) :
    productKeyApex s ∈ frontier polygonProductKeyBody :=
  product_key_graph_window_subset_frontier s (product_key_apex_mem_graph_window s)

/-- A witnessed point in the interior of the actual bounded body. The already
proved local graph at a concrete apex supplies a strictly inward displacement. -/
theorem polygon_product_key_body_interior_nonempty :
    (interior polygonProductKeyBody).Nonempty := by
  let s : ProductKeySite := (0, 0, false)
  let G := polygonProductKeyBody_graph_window_local_graph s (productKeyApex s)
    (product_key_apex_mem_graph_window s)
  have ht : 0 < G.radius / 2 := by linarith [G.radius_pos]
  have htr : |G.radius / 2| < G.radius := by
    rw [abs_of_pos ht]
    linarith [G.radius_pos]
  have hpoint := G.interior_above 0 (G.radius / 2) (by simp)
    (by simpa only [norm_zero] using G.radius_pos) htr
    (by simpa only [G.height_zero] using ht)
  exact ⟨_, hpoint⟩

end
end SpectreGeometry
