module

public import SpectreGeometry.PolygonProductKeyCollarSeparation
public import SpectreGeometry.PolygonProductKeyHypographs
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section


/-! The literal bounded 56-key body obtained from the optimized P×P recipe.

The carrier is the actual polygon product, the replacement regions are the
actual pairwise disjoint closed recipe collars, and the inserted pieces are
the actual signed max-min hypographs. The normal coordinate is outward:
the raw carrier has coordinate z ≤ 0, and each replaced graph has z ≤ h.

All local charts below belong to this literal set. No tiling, recognition,
registration, or global boundary classification is asserted here. -/
namespace SpectreGeometry
noncomputable section
open Set PhysicalRegistration
open scoped InnerProductSpace

/-- Literal finite replacement, with exactly the optimized 56 recipe sites. -/
def polygonProductKeyBody : Set EFour :=
  replaceTubes polygonProductBody productKeyCollar productKeyHypograph

theorem polygon_product_key_body_eq_replaceTubes :
    polygonProductKeyBody =
      replaceTubes polygonProductBody productKeyCollar productKeyHypograph := rfl

theorem polygon_product_body_isCompact : IsCompact polygonProductBody :=
  (polygonBody_compact.prod polygonBody_compact).image productCoordinates.continuous

theorem polygon_product_key_body_isClosed : IsClosed polygonProductKeyBody :=
  replaceTubes_isClosed polygonProductBody productKeyCollar productKeyHypograph
    polygon_product_body_isCompact.isClosed product_key_collar_isClosed
    product_key_hypograph_closed

theorem product_key_collar_isCompact (s : ProductKeySite) :
    IsCompact (productKeyCollar s) := by
  apply (isCompact_closedBall (productKeyCenter s) (1 / 10000 : ℝ)).of_isClosed_subset
    (product_key_collar_isClosed s)
  intro x hx
  exact product_key_collar_dist s x hx

theorem polygon_product_key_body_isCompact : IsCompact polygonProductKeyBody :=
  (polygon_product_body_isCompact.diff (isOpen_iUnion fun _ => isOpen_interior)).union
    (isCompact_iUnion fun s : ProductKeySite => (product_key_collar_isCompact s).inter_right
      (product_key_hypograph_closed s))

theorem polygon_product_key_body_isBounded : Bornology.IsBounded polygonProductKeyBody :=
  polygon_product_key_body_isCompact.isBounded

/-- Exact frame coordinates, with the fourth column equal to the outward normal. -/
theorem product_key_affine_frame_coordinate (s : ProductKeySite) (w : EFour) (j : Fin 4) :
    inner ℝ (productKeyFrame s j) (productKeyAffineIsometry s w - productKeyCenter s) =
      w j := by
  rw [productKeyAffineIsometry_apply, add_sub_cancel_left]
  simp [inner_sum, real_inner_smul_right, productKeyFrame_inner, mul_ite]

theorem product_key_inverse_frame_coordinate (s : ProductKeySite) (x : EFour) (j : Fin 4) :
    inner ℝ (productKeyFrame s j) (x - productKeyCenter s) =
      (productKeyAffineIsometry s).symm x j := by
  simpa only [AffineIsometryEquiv.apply_symm_apply] using
    product_key_affine_frame_coordinate s ((productKeyAffineIsometry s).symm x) j

theorem product_key_inverse_tangent_coordinate (s : ProductKeySite) (x : EFour) (j : Fin 3) :
    inner ℝ (productKeyTangent s j) (x - productKeyCenter s) =
      (productKeyAffineIsometry s).symm x j.castSucc := by
  simpa only [productKeyFrame_tangent] using
    product_key_inverse_frame_coordinate s x j.castSucc

theorem product_key_inverse_normal_coordinate (s : ProductKeySite) (x : EFour) :
    inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s) =
      (productKeyAffineIsometry s).symm x 3 := by
  simpa only [productKeyFrame_normal] using product_key_inverse_frame_coordinate s x 3

/-- The carrier lies on the nonpositive side of the explicitly outward normal. -/
theorem product_key_collar_carrier_outward (s : ProductKeySite) (x : EFour)
    (hx : x ∈ productKeyCollar s) :
    (x ∈ polygonProductBody ↔ inner ℝ (productKeyOutwardNormal s)
      (x - productKeyCenter s) ≤ 0) ∧
    (x ∈ interior polygonProductBody ↔ inner ℝ (productKeyOutwardNormal s)
      (x - productKeyCenter s) < 0) := by
  rw [product_key_inverse_normal_coordinate]
  exact product_key_collar_carrier s x hx

/-- The zero-extended max-min profile is everywhere in [0,1]. -/
theorem product_key_tent_profile_bounds (s : ProductKeySite) (v : EFour) :
    0 ≤ keyTentProfile productKeyEta
      (fun j => (productKeyPrime j false : ℝ)) (fun j => (productKeyPrime j true : ℝ))
      (productKeyTangent s) v ∧
    keyTentProfile productKeyEta
      (fun j => (productKeyPrime j false : ℝ)) (fun j => (productKeyPrime j true : ℝ))
      (productKeyTangent s) v ≤ 1 := by
  have heta : 0 < productKeyEta := by norm_num [productKeyEta]
  have hm : 0 ≤ (productKeyPrime 0 false : ℝ) := Nat.cast_nonneg _
  have hp : 0 ≤ (productKeyPrime 0 true : ℝ) := Nat.cast_nonneg _
  unfold keyTentProfile
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  apply (finiteLowerEnvelope_le _ v (0 : Fin 3)).trans
  by_cases hv : 0 ≤ inner ℝ (productKeyTangent s 0) v
  · apply (min_le_right _ _).trans
    have hnonneg := div_nonneg (mul_nonneg hp hv) heta.le
    linarith
  · apply (min_le_left _ _).trans
    have hnonpos := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hm (le_of_not_ge hv)) heta.le
    linarith

/-- The exact global height bound uses both signs of the labels, with |label| ≤ 2. -/
theorem product_key_height_amplitude (s : ProductKeySite) (v : EFour) :
    |productKeyHeight s v| ≤ productKeyEta * 2 / (productKeyN : ℝ) := by
  have hp := product_key_tent_profile_bounds s v
  have heta : 0 < productKeyEta := by norm_num [productKeyEta]
  have hN : 0 < (productKeyN : ℝ) := by norm_num [productKeyN]
  unfold productKeyHeight keyHeight
  rw [abs_mul, abs_div, abs_mul, abs_of_pos heta, abs_of_pos hN, abs_of_nonneg hp.1]
  calc
    productKeyEta * |(productKeySignedLabel s : ℝ)| / (productKeyN : ℝ) *
        keyTentProfile productKeyEta
          (fun j => (productKeyPrime j false : ℝ)) (fun j => (productKeyPrime j true : ℝ))
          (productKeyTangent s) v
        ≤ productKeyEta * |(productKeySignedLabel s : ℝ)| / (productKeyN : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hp.2
        (div_nonneg (mul_nonneg heta.le (abs_nonneg _)) hN.le)
    _ ≤ productKeyEta * 2 / (productKeyN : ℝ) := by
      rw [mul_one]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (product_key_label_bound s) heta.le) hN.le

theorem product_key_height_below_rho (s : ProductKeySite) (v : EFour) :
    |productKeyHeight s v| < productKeyRho :=
  (product_key_height_amplitude s v).trans_lt (by norm_num [productKeyEta, productKeyN, productKeyRho])

/-- The strict open box in the actual physical frame. -/
def productKeyStrictCollar (s : ProductKeySite) : Set EFour :=
  {x | (∀ j : Fin 3, |inner ℝ (productKeyTangent s j) (x - productKeyCenter s)| <
    2 * productKeyEta) ∧
    |inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s)| < productKeyRho}

theorem product_key_strict_collar_isOpen (s : ProductKeySite) :
    IsOpen (productKeyStrictCollar s) := by
  have ht (j : Fin 3) : Continuous
      (fun x : EFour => |inner ℝ (productKeyTangent s j) (x - productKeyCenter s)|) :=
    ((unit_inner_continuous _ (productKeyTangent_norm s j)).comp
      (continuous_id.sub continuous_const)).abs
  have hn : Continuous
      (fun x : EFour => |inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s)|) :=
    ((unit_inner_continuous _ (productKeyOutwardNormal_norm s)).comp
      (continuous_id.sub continuous_const)).abs
  simp only [productKeyStrictCollar, ofPred_and, ofPred_forall]
  exact (isOpen_iInter_of_finite fun j => isOpen_lt (ht j) continuous_const).inter
    (isOpen_lt hn continuous_const)

theorem product_key_strict_collar_subset (s : ProductKeySite) :
    productKeyStrictCollar s ⊆ productKeyCollar s := by
  intro x hx
  refine ⟨(productKeyAffineIsometry s).symm x, ?_,
    (productKeyAffineIsometry s).apply_symm_apply x⟩
  constructor
  · intro j
    rw [← product_key_inverse_tangent_coordinate]
    exact (hx.1 j).le
  · rw [← product_key_inverse_normal_coordinate]
    exact hx.2.le

theorem product_key_strict_collar_subset_interior (s : ProductKeySite) :
    productKeyStrictCollar s ⊆ interior (productKeyCollar s) :=
  interior_maximal (product_key_strict_collar_subset s) (product_key_strict_collar_isOpen s)

/-- A closed tangent window containing the entire active key footprint. -/
def productKeyGraphWindow (s : ProductKeySite) : Set EFour :=
  productKeyGraph s ∩ {x | ∀ j : Fin 3,
    |inner ℝ (productKeyTangent s j) (x - productKeyCenter s)| ≤ productKeyEta}

theorem product_key_graph_window_subset_interior_collar (s : ProductKeySite) :
    productKeyGraphWindow s ⊆ interior (productKeyCollar s) := by
  intro x hx
  apply product_key_strict_collar_subset_interior s
  constructor
  · intro j
    exact (hx.2 j).trans_lt (by norm_num [productKeyEta])
  · have hgraph := hx.1
    change inner ℝ (productKeyOutwardNormal s) (x - productKeyCenter s) =
      productKeyHeight s (x - productKeyCenter s) at hgraph
    rw [hgraph]
    exact product_key_height_below_rho s (x - productKeyCenter s)

theorem product_key_active_graph_mem_window (s : ProductKeySite) (x : EFour)
    (hx : x ∈ productKeyGraph s)
    (hactive : productKeyHeight s (x - productKeyCenter s) ≠ 0) :
    x ∈ productKeyGraphWindow s :=
  ⟨hx, product_key_height_support s (x - productKeyCenter s) hactive⟩

private theorem product_key_collar_interior_disjoint (s t : ProductKeySite) (hne : t ≠ s) :
    Disjoint (interior (productKeyCollar s)) (productKeyCollar t) :=
  (product_key_collars_disjoint s t hne.symm).mono_left interior_subset

/-- Within an actual collar interior, the literal body is exactly its keyed hypograph. -/
theorem polygon_product_key_body_local_iff (s : ProductKeySite) (x : EFour)
    (hx : x ∈ interior (productKeyCollar s)) :
    x ∈ polygonProductKeyBody ↔ x ∈ productKeyHypograph s :=
  replaceTubes_local_iff polygonProductBody productKeyCollar productKeyHypograph s
    (interior (productKeyCollar s)) (product_key_collar_interior_disjoint s)
    (fun _ hy hn => (hn hy).elim) x hx

theorem polygon_product_key_body_local_outward_iff (s : ProductKeySite) (x : EFour)
    (hx : x ∈ interior (productKeyCollar s)) :
    x ∈ polygonProductKeyBody ↔ inner ℝ (productKeyOutwardNormal s)
      (x - productKeyCenter s) ≤ productKeyHeight s (x - productKeyCenter s) :=
  polygon_product_key_body_local_iff s x hx

/-- Every actual graph point inside its collar has an inward Lipschitz chart
on the literal bounded body, with the recipe's exact constant 34/4357. -/
def polygonProductKeyBody_local_graph (s : ProductKeySite) (x : EFour)
    (hxgraph : x ∈ productKeyGraph s) (hx : x ∈ interior (productKeyCollar s)) :
    LocalLipschitzGraphAt polygonProductKeyBody x (34 / 4357) :=
  replaceTubes_local_graph polygonProductBody productKeyCollar productKeyHypograph s
    (productKeyGraph_local_graph s x hxgraph) (interior (productKeyCollar s))
    isOpen_interior hx (product_key_collar_interior_disjoint s)
    (fun _ hy hn => (hn hy).elim)

/-- The entire concrete key-graph window lies in the local-graph region. -/
def polygonProductKeyBody_graph_window_local_graph (s : ProductKeySite) (x : EFour)
    (hx : x ∈ productKeyGraphWindow s) :
    LocalLipschitzGraphAt polygonProductKeyBody x (34 / 4357) :=
  polygonProductKeyBody_local_graph s x hx.1
    (product_key_graph_window_subset_interior_collar s hx)

theorem product_key_graph_window_subset_body (s : ProductKeySite) :
    productKeyGraphWindow s ⊆ polygonProductKeyBody := by
  intro x hx
  apply (polygon_product_key_body_local_outward_iff s x
    (product_key_graph_window_subset_interior_collar s hx)).mpr
  exact hx.1.le

end
end SpectreGeometry
