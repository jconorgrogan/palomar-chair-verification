module

public import PhysicalRegistration.CrossTilingGenericity
public import PhysicalRegistration.CreaseNormalSpan
public import PhysicalRegistration.KeyTransverseClassification
public import PhysicalRegistration.CarrierTransverse

@[expose] public section

/-!
# Actual incident-key strata at dense placed crease points

The finite-neighbor genericity construction and the literal crease normal-span
computations together force every incident boundary plane into the root
crease's two-normal span. Pulling that span through each neighboring placement
classifies all actual native key-graph incidences, without a contact, inventory,
or transverse-rank hypothesis.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

/-- Every boundary plane of any incident placed body at the selected dense
base-crease points has its normal in the actual placed root two-normal span. -/
theorem genericBaseCrease_incident_boundary_normal_span
    {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (i : ι) (u : Site m) (s : Side m) :
    ∃ D : Set (Space m), D ⊆ f i '' genericBaseCrease a u s ∧
      closure D = f i '' baseCrease a u s ∧
      ∀ x ∈ D, ∀ j, x ∈ placedBody a (f j) →
        ∀ b : BoundaryPlaneIndex m, x ∈ f j '' boundaryPlane a b →
          placedNormal (f j) (boundaryPlaneNormal a b) ∈ Submodule.span ℝ
            {placedNormal (f i) (outward u.1), placedNormal (f i) (sideNormal a u s)} := by
  obtain ⟨D, hDG, hDC, _, hplanes⟩ :=
    genericBaseCrease_crossPlacement a f hdisjoint i u s
  refine ⟨D, hDG, hDC, ?_⟩
  intro x hx j hj b hb
  apply placed_baseCrease_containing_normal_mem_span a u s (f i)
    (placedNormal (f j) (boundaryPlaneNormal a b))
    (boundaryPlaneLevel a b +
      ⟪placedNormal (f j) (boundaryPlaneNormal a b), f j (boundaryPlaneCenter b)⟫_ℝ)
  intro y hy
  have h := hplanes x hx j hj b hb hy
  rwa [image_boundaryPlane_eq_uncentered] at h

/-- The analogous endpoint for an actual distinct-axis side crease. -/
theorem genericSideCrease_incident_boundary_normal_span
    {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (i : ι) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    ∃ D : Set (Space m), D ⊆ f i '' genericSideCrease a u s t ∧
      closure D = f i '' sideCrease a u s t ∧
      ∀ x ∈ D, ∀ j, x ∈ placedBody a (f j) →
        ∀ b : BoundaryPlaneIndex m, x ∈ f j '' boundaryPlane a b →
          placedNormal (f j) (boundaryPlaneNormal a b) ∈ Submodule.span ℝ
            {placedNormal (f i) (sideNormal a u s), placedNormal (f i) (sideNormal a u t)} := by
  obtain ⟨D, hDG, hDC, _, hplanes⟩ :=
    genericSideCrease_crossPlacement a f hdisjoint i u s t hst
  refine ⟨D, hDG, hDC, ?_⟩
  intro x hx j hj b hb
  apply placed_sideCrease_containing_normal_mem_span a u s t hst (f i)
    (placedNormal (f j) (boundaryPlaneNormal a b))
    (boundaryPlaneLevel a b +
      ⟪placedNormal (f j) (boundaryPlaneNormal a b), f j (boundaryPlaneCenter b)⟫_ℝ)
  intro y hy
  have h := hplanes x hx j hj b hb hy
  rwa [image_boundaryPlane_eq_uncentered] at h

/-- Pulling a proved world-space span back through an arbitrary placement. -/
theorem normal_mem_span_pair_of_placedNormal_mem_span
    {m : ℕ} (f : Space m ≃ᵢ Space m) (n p q : Space m)
    (h : placedNormal f n ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    n ∈ Submodule.span ℝ
      {f.toRealAffineIsometryEquiv.linearIsometryEquiv.symm p,
       f.toRealAffineIsometryEquiv.linearIsometryEquiv.symm q} := by
  obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp h
  apply Submodule.mem_span_pair.mpr
  refine ⟨r, s, ?_⟩
  have heq := congrArg f.toRealAffineIsometryEquiv.linearIsometryEquiv.symm hrs
  simpa only [map_add, map_smul, placedNormal,
    LinearIsometryEquiv.symm_apply_apply] using heq

/-- Zero normal height puts the point on its literal integer carrier plane,
whose normal gives the native outward normal by scalar multiplication. -/
theorem normalCoord_zero_boundaryPlane
    {m J : ℕ} (a : Coefficients m J) (u : Site m) (y : Space m)
    (hy : normalCoord u y = 0) :
    ∃ k : Fin 3, y ∈ boundaryPlane a (.inl (normalIndex u.1, k)) ∧
      outward u.1 = normalSign u.1 •
        boundaryPlaneNormal a (.inl (normalIndex u.1, k)) := by
  have hsign : normalSign u.1 ≠ 0 := by
    intro hz
    have habs := abs_normalSign u.1
    rw [hz, abs_zero] at habs
    norm_num at habs
  have hprod : normalSign u.1 *
      (y (normalIndex u.1) - siteCenter u (normalIndex u.1)) = 0 := by
    simpa only [normalCoord, outward_inner_coordinate, PiLp.sub_apply] using hy
  have hcoord : y (normalIndex u.1) = (facetPlane u.1 : ℝ) := by
    rw [← siteCenter_normal u]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hsign)
  have hlevel : ∃ k : Fin 3, (facetPlane u.1 : ℝ) = (k.val : ℝ) := by
    cases h : u.1 with
    | inl ai =>
      rcases ai with ⟨c, i⟩
      cases hc : c.val i
      · exact ⟨0, by simp [facetPlane, hc]⟩
      · exact ⟨2, by simp [facetPlane, hc]⟩
    | inr i => exact ⟨1, by simp [facetPlane]⟩
  obtain ⟨k, hk⟩ := hlevel
  exact ⟨k, hcoord.trans hk, rfl⟩

/-- Incident boundary-plane span control is sufficient for the actual native
key-graph classification after an arbitrary ambient isometric placement. -/
theorem placed_keyGraph_stratum_of_boundary_normal_span
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (u : Site m) (x p q : Space m)
    (hx : f.symm x ∈ keyGraph a u)
    (hplanes : ∀ b : BoundaryPlaneIndex m, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    (∃ s : Side m, f.symm x ∈ strictBranchRegion J u s) ∨
    (∃ s : Side m, f.symm x ∈ genericBaseCrease a u s) ∨
    (∃ s t : Side m, s.1 ≠ t.1 ∧ f.symm x ∈ genericSideCrease a u s t) := by
  apply keyGraph_transverse_stratum_classification hm a u (f.symm x)
    (f.toRealAffineIsometryEquiv.linearIsometryEquiv.symm p)
    (f.toRealAffineIsometryEquiv.linearIsometryEquiv.symm q) hx
  · intro s hs
    apply normal_mem_span_pair_of_placedNormal_mem_span f (sideNormal a u s) p q
    exact hplanes (.inr (u, s)) ⟨f.symm x, sideFace_plane a u s _ hs,
      f.apply_symm_apply x⟩
  · intro hzero
    obtain ⟨k, hk, hn⟩ := normalCoord_zero_boundaryPlane a u (f.symm x) hzero
    have hnormal := hplanes (.inl (normalIndex u.1, k))
      ⟨f.symm x, hk, f.apply_symm_apply x⟩
    have hnative := normal_mem_span_pair_of_placedNormal_mem_span f _ p q hnormal
    rw [hn]
    exact Submodule.smul_mem _ _ hnative

/-- Actual dense root base-crease points classify every neighboring native
key graph through the selected point. No transverse-span hypothesis remains. -/
theorem genericBaseCrease_incident_key_classification
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (i : ι) (u : Site m) (s : Side m) :
    ∃ D : Set (Space m), D ⊆ f i '' genericBaseCrease a u s ∧
      closure D = f i '' baseCrease a u s ∧
      ∀ x ∈ D, ∀ j, ∀ v : Site m, (f j).symm x ∈ keyGraph a v →
        (∃ r : Side m, (f j).symm x ∈ strictBranchRegion J v r) ∨
        (∃ r : Side m, (f j).symm x ∈ genericBaseCrease a v r) ∨
        (∃ r t : Side m, r.1 ≠ t.1 ∧ (f j).symm x ∈ genericSideCrease a v r t) := by
  obtain ⟨D, hDG, hDC, hnormals⟩ :=
    genericBaseCrease_incident_boundary_normal_span a f hdisjoint i u s
  refine ⟨D, hDG, hDC, ?_⟩
  intro x hx j v hv
  apply placed_keyGraph_stratum_of_boundary_normal_span hm a (f j) v x
    (placedNormal (f i) (outward u.1)) (placedNormal (f i) (sideNormal a u s)) hv
  exact hnormals x hx j ⟨(f j).symm x, keyGraph_subset_body a v hv,
    (f j).apply_symm_apply x⟩

/-- Actual dense distinct-axis root side-crease points classify every native
key graph of every arbitrary placed copy through the selected point. -/
theorem genericSideCrease_incident_key_classification
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (i : ι) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    ∃ D : Set (Space m), D ⊆ f i '' genericSideCrease a u s t ∧
      closure D = f i '' sideCrease a u s t ∧
      ∀ x ∈ D, ∀ j, ∀ v : Site m, (f j).symm x ∈ keyGraph a v →
        (∃ r : Side m, (f j).symm x ∈ strictBranchRegion J v r) ∨
        (∃ r : Side m, (f j).symm x ∈ genericBaseCrease a v r) ∨
        (∃ r t : Side m, r.1 ≠ t.1 ∧ (f j).symm x ∈ genericSideCrease a v r t) := by
  obtain ⟨D, hDG, hDC, hnormals⟩ :=
    genericSideCrease_incident_boundary_normal_span a f hdisjoint i u s t hst
  refine ⟨D, hDG, hDC, ?_⟩
  intro x hx j v hv
  apply placed_keyGraph_stratum_of_boundary_normal_span hm a (f j) v x
    (placedNormal (f i) (sideNormal a u s)) (placedNormal (f i) (sideNormal a u t)) hv
  exact hnormals x hx j ⟨(f j).symm x, keyGraph_subset_body a v hv,
    (f j).apply_symm_apply x⟩

/-- Every active carrier coordinate direction pulls back from one of the
literal incident boundary planes, so no three coordinate axes can be active. -/
theorem placed_activeCarrierAxes_card_le_two_of_boundary_normal_span
    {m J : ℕ} (a : Coefficients m J) (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hplanes : ∀ b : BoundaryPlaneIndex m, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    (activeCarrierAxes (f.symm x)).card ≤ 2 := by
  apply activeCarrierAxes_card_le_two (f.symm x)
    (f.toRealAffineIsometryEquiv.linearIsometryEquiv.symm p)
    (f.toRealAffineIsometryEquiv.linearIsometryEquiv.symm q)
  intro i hi
  have hcoord : (f.symm x) i = 0 ∨ (f.symm x) i = 1 ∨ (f.symm x) i = 2 := by
    simpa only [activeCarrierAxes, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  have hlevel : ∃ k : Fin 3, (f.symm x) i = (k.val : ℝ) := by
    rcases hcoord with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  obtain ⟨k, hk⟩ := hlevel
  exact normal_mem_span_pair_of_placedNormal_mem_span f _ p q
    (hplanes (.inl (i, k)) ⟨f.symm x, hk, f.apply_symm_apply x⟩)

/-- At a genuine boundary point outside every key graph, the actual body has
an open carrier-sign germ on at most two orthogonal native coordinate axes. -/
theorem placed_ordinary_boundary_germ_of_boundary_normal_span
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hx : f.symm x ∈ frontier (body a))
    (hkey : ∀ u, f.symm x ∉ keyGraph a u)
    (hplanes : ∀ b : BoundaryPlaneIndex m, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    (activeCarrierAxes (f.symm x)).card ≤ 2 ∧
    ∃ U : Set (Space m), IsOpen U ∧ f.symm x ∈ U ∧
      (∀ y ∈ U, y ∈ body a ↔ y ∈ carrier m) ∧
      ∀ y ∈ U, ∀ z ∈ U,
        (∀ i ∈ activeCarrierAxes (f.symm x),
          (y i ≤ (f.symm x) i ↔ z i ≤ (f.symm x) i) ∧
          ((f.symm x) i ≤ y i ↔ (f.symm x) i ≤ z i)) →
        (y ∈ body a ↔ z ∈ body a) := by
  refine ⟨placed_activeCarrierAxes_card_le_two_of_boundary_normal_span a f x p q hplanes, ?_⟩
  obtain ⟨_, U, hU, hxU, _, heq⟩ := frontier_body_outside_keyGraphs hm a (f.symm x) hx hkey
  have hxbody : f.symm x ∈ body a := (body_isClosed a).frontier_subset hx
  have hxcarrier : f.symm x ∈ carrier m := (heq _ hxU).mp hxbody
  obtain ⟨V, hV, hxV, hsign⟩ := carrier_local_active_sign_germ (f.symm x) hxcarrier
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_, ?_⟩
  · intro y hy
    exact heq y hy.1
  · intro y hy z hz h
    rw [heq y hy.1, heq z hz.1]
    exact hsign y hy.2 z hz.2 h

/-- A dense actual base crease also controls all untouched incident boundary
points. Their body germs depend on at most two native orthogonal axes. -/
theorem genericBaseCrease_incident_ordinary_boundary_germ
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (i : ι) (u : Site m) (s : Side m) :
    ∃ D : Set (Space m), D ⊆ f i '' genericBaseCrease a u s ∧
      closure D = f i '' baseCrease a u s ∧
      ∀ x ∈ D, ∀ j, (f j).symm x ∈ frontier (body a) →
        (∀ v, (f j).symm x ∉ keyGraph a v) →
        (activeCarrierAxes ((f j).symm x)).card ≤ 2 ∧
        ∃ U : Set (Space m), IsOpen U ∧ (f j).symm x ∈ U ∧
          (∀ y ∈ U, y ∈ body a ↔ y ∈ carrier m) ∧
          ∀ y ∈ U, ∀ z ∈ U,
            (∀ k ∈ activeCarrierAxes ((f j).symm x),
              (y k ≤ ((f j).symm x) k ↔ z k ≤ ((f j).symm x) k) ∧
              (((f j).symm x) k ≤ y k ↔ ((f j).symm x) k ≤ z k)) →
            (y ∈ body a ↔ z ∈ body a) := by
  obtain ⟨D, hDG, hDC, hnormals⟩ :=
    genericBaseCrease_incident_boundary_normal_span a f hdisjoint i u s
  refine ⟨D, hDG, hDC, ?_⟩
  intro x hx j hj hkey
  apply placed_ordinary_boundary_germ_of_boundary_normal_span hm a (f j) x
    (placedNormal (f i) (outward u.1)) (placedNormal (f i) (sideNormal a u s)) hj hkey
  exact hnormals x hx j ⟨(f j).symm x, (body_isClosed a).frontier_subset hj,
    (f j).apply_symm_apply x⟩

/-- The untouched-boundary corollary for a dense actual distinct-axis side
crease, again with arbitrary ambient placements and no supplied span bound. -/
theorem genericSideCrease_incident_ordinary_boundary_germ
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (i : ι) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    ∃ D : Set (Space m), D ⊆ f i '' genericSideCrease a u s t ∧
      closure D = f i '' sideCrease a u s t ∧
      ∀ x ∈ D, ∀ j, (f j).symm x ∈ frontier (body a) →
        (∀ v, (f j).symm x ∉ keyGraph a v) →
        (activeCarrierAxes ((f j).symm x)).card ≤ 2 ∧
        ∃ U : Set (Space m), IsOpen U ∧ (f j).symm x ∈ U ∧
          (∀ y ∈ U, y ∈ body a ↔ y ∈ carrier m) ∧
          ∀ y ∈ U, ∀ z ∈ U,
            (∀ k ∈ activeCarrierAxes ((f j).symm x),
              (y k ≤ ((f j).symm x) k ↔ z k ≤ ((f j).symm x) k) ∧
              (((f j).symm x) k ≤ y k ↔ ((f j).symm x) k ≤ z k)) →
            (y ∈ body a ↔ z ∈ body a) := by
  obtain ⟨D, hDG, hDC, hnormals⟩ :=
    genericSideCrease_incident_boundary_normal_span a f hdisjoint i u s t hst
  refine ⟨D, hDG, hDC, ?_⟩
  intro x hx j hj hkey
  apply placed_ordinary_boundary_germ_of_boundary_normal_span hm a (f j) x
    (placedNormal (f i) (sideNormal a u s)) (placedNormal (f i) (sideNormal a u t)) hj hkey
  exact hnormals x hx j ⟨(f j).symm x, (body_isClosed a).frontier_subset hj,
    (f j).apply_symm_apply x⟩

#print axioms genericBaseCrease_incident_boundary_normal_span
#print axioms genericSideCrease_incident_boundary_normal_span
#print axioms normal_mem_span_pair_of_placedNormal_mem_span
#print axioms normalCoord_zero_boundaryPlane
#print axioms placed_keyGraph_stratum_of_boundary_normal_span
#print axioms genericBaseCrease_incident_key_classification
#print axioms genericSideCrease_incident_key_classification

#print axioms placed_activeCarrierAxes_card_le_two_of_boundary_normal_span
#print axioms placed_ordinary_boundary_germ_of_boundary_normal_span
#print axioms genericBaseCrease_incident_ordinary_boundary_germ
#print axioms genericSideCrease_incident_ordinary_boundary_germ

end
end PhysicalRegistration.NativeChair
