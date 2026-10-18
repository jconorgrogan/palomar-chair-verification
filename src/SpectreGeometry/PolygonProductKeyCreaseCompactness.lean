module

public import SpectreGeometry.PolygonProductKeyCreaseConnectivity
public import SpectreGeometry.PolygonProductKeyFrontier

@[expose] public section


/-! Compact actual crease complexes, with quantitative collar admission and
actual-frontier inclusion. Every bound is derived from the literal branch
inequalities; closedness, compactness and disjointness are not extra premises. -/
namespace SpectreGeometry.ProductCrease
noncomputable section
open SpectreGeometry PhysicalRegistration Set
open scoped InnerProductSpace

theorem branchRegion_tangent_bound (u : ProductKeySite) (b : ProductKeySide)
    (x : EFour) (hx : x ∈ productKeyBranchRegion u b) (j : Fin 3) :
    |inner ℝ (productKeyTangent u j) (x-productKeyCenter u)| ≤ productKeyEta := by
  have heta : 0 < productKeyEta := by norm_num [productKeyEta]
  have hm := (product_key_prime_bounds j false).1
  have hp := (product_key_prime_bounds j true).1
  have hm0 : 0 < (productKeyPrime j false : ℝ) := by linarith
  have hp0 : 0 < (productKeyPrime j true : ℝ) := by linarith
  have hlo := hx.1.trans (hx.2 (j,false))
  have hhi := hx.1.trans (hx.2 (j,true))
  change 0 ≤ productKeyBranchProfile u (j,false) x at hlo
  change 0 ≤ productKeyBranchProfile u (j,true) x at hhi
  simp only [productKeyBranchProfile, Bool.false_eq_true, if_false, one_mul] at hlo
  simp only [productKeyBranchProfile, if_true, neg_one_mul, neg_mul, neg_div, one_mul] at hhi
  have hlo' : -(1:ℝ) ≤ (productKeyPrime j false : ℝ) *
      inner ℝ (productKeyTangent u j) (x-productKeyCenter u) / productKeyEta := by linarith
  have hhi' : (productKeyPrime j true : ℝ) *
      inner ℝ (productKeyTangent u j) (x-productKeyCenter u) / productKeyEta ≤ 1 := by linarith
  have hml := (le_div_iff₀ heta).mp hlo'
  have hmh := (div_le_iff₀ heta).mp hhi'
  have hl : -productKeyEta / (productKeyPrime j false : ℝ) ≤
      inner ℝ (productKeyTangent u j) (x-productKeyCenter u) :=
    (div_le_iff₀ hm0).mpr (by nlinarith)
  have hh : inner ℝ (productKeyTangent u j) (x-productKeyCenter u) ≤
      productKeyEta / (productKeyPrime j true : ℝ) :=
    (le_div_iff₀ hp0).mpr (by nlinarith)
  have hlb : productKeyEta / (productKeyPrime j false : ℝ) ≤ productKeyEta :=
    (div_le_iff₀ hm0).mpr (by nlinarith)
  have hhb : productKeyEta / (productKeyPrime j true : ℝ) ≤ productKeyEta :=
    (div_le_iff₀ hp0).mpr (by nlinarith)
  rw [neg_div] at hl
  exact abs_le.mpr ⟨by linarith,hh.trans hhb⟩

theorem sideFace_subset_graphWindow (u : ProductKeySite) (b : ProductKeySide) :
    productKeySideFace u b ⊆ productKeyGraphWindow u := by
  intro x hx
  exact ⟨hx.1,fun j => branchRegion_tangent_bound u b x hx.2 j⟩

theorem branchProfile_continuous (u : ProductKeySite) (b : ProductKeySide) :
    Continuous (productKeyBranchProfile u b) := by
  unfold productKeyBranchProfile
  fun_prop

theorem branchRegion_isClosed (u : ProductKeySite) (b : ProductKeySide) :
    IsClosed (productKeyBranchRegion u b) := by
  unfold productKeyBranchRegion
  simp only [ofPred_and,ofPred_forall]
  exact (isClosed_le continuous_const (branchProfile_continuous u b)).inter
    (isClosed_iInter fun c => isClosed_le (branchProfile_continuous u b)
      (branchProfile_continuous u c))

theorem graph_isClosed (u : ProductKeySite) : IsClosed (productKeyGraph u) :=
  isClosed_eq
    ((unit_inner_continuous _ (productKeyOutwardNormal_norm u)).comp
      (continuous_id.sub continuous_const))
    ((product_key_height_continuous u).comp (continuous_id.sub continuous_const))

theorem sideFace_isClosed (u : ProductKeySite) (b : ProductKeySide) :
    IsClosed (productKeySideFace u b) :=
  (graph_isClosed u).inter (branchRegion_isClosed u b)

theorem sideFace_isCompact (u : ProductKeySite) (b : ProductKeySide) :
    IsCompact (productKeySideFace u b) :=
  (product_key_collar_isCompact u).of_isClosed_subset (sideFace_isClosed u b)
    ((sideFace_subset_graphWindow u b).trans
      ((product_key_graph_window_subset_interior_collar u).trans interior_subset))

theorem baseCrease_isCompact (u : ProductKeySite) (b : ProductKeySide) :
    IsCompact (baseCrease u b) :=
  (sideFace_isCompact u b).inter_right
    (isClosed_eq (by unfold normalCoord; fun_prop) continuous_const)

theorem sideCrease_isCompact (u : ProductKeySite) (b c : ProductKeySide) :
    IsCompact (sideCrease u b c) :=
  (sideFace_isCompact u b).inter_right (sideFace_isClosed u c)

theorem creaseComplex_isCompact (u : ProductKeySite) : IsCompact (creaseComplex u) :=
  (isCompact_iUnion (baseCrease_isCompact u)).union
    (isCompact_iUnion fun b => isCompact_iUnion fun c => sideCrease_isCompact u b c.val)

theorem creaseComplex_subset_graphWindow (u : ProductKeySite) :
    creaseComplex u ⊆ productKeyGraphWindow u := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    exact sideFace_subset_graphWindow u b hb.1
  · obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    obtain ⟨c,hc⟩ := mem_iUnion.mp hb
    exact sideFace_subset_graphWindow u b hc.1

theorem creaseComplex_subset_frontier (u : ProductKeySite) :
    creaseComplex u ⊆ frontier polygonProductKeyBody :=
  (creaseComplex_subset_graphWindow u).trans (product_key_graph_window_subset_frontier u)

theorem creaseComplex_pairwise_disjoint :
    Pairwise (fun u v : ProductKeySite => Disjoint (creaseComplex u) (creaseComplex v)) := by
  intro u v huv
  apply (product_key_collars_disjoint u v huv).mono
  · exact (creaseComplex_subset_graphWindow u).trans
      ((product_key_graph_window_subset_interior_collar u).trans interior_subset)
  · exact (creaseComplex_subset_graphWindow v).trans
      ((product_key_graph_window_subset_interior_collar v).trans interior_subset)

end
end SpectreGeometry.ProductCrease
