module

public import SparseMonotiles.PhysicalSectorConsequences
public import SparseMonotiles.FaceCompanionContinuation

@[expose] public section

/-! A genuine two-tile partition identifies the opposite material halfspace.
Regularity comes from the actual incident sector inventory, rather than an
assumption that a companion is already flat or has the expected orientation. -/
namespace SparseMonotiles
open Set SectorAngleSum

/-- A regular closed companion in a nonoverlapping cover is the opposite
halfspace. Any lower-dimensional spurious additions are excluded by regularity. -/
theorem regular_closed_companion_of_halfspace_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : E) (hn : n ≠ 0) (S : Set E)
    (hclosed : IsClosed S) (hreg : closure (interior S) = S)
    (hcover : ∀ x, x ∈ normalHalfspace n ∨ x ∈ S)
    (hdis : Disjoint (interior (normalHalfspace n)) (interior S)) :
    S = normalHalfspace (-n) := by
  have hdis' : Disjoint (interior (normalHalfspace n)) S := by
    simpa only [hreg] using hdis.closure_right isOpen_interior
  have hneg : closure {x : E | inner (𝕜 := ℝ) n x < 0} = normalHalfspace (-n) := by
    have h := closure_neg_of_perturbation (fun x : E => inner (𝕜 := ℝ) n x)
      (continuous_const.inner continuous_id) (-n) (inner (𝕜 := ℝ) n n)
      (real_inner_self_pos.mpr hn) (by intro x t; simp [inner_add_right,inner_smul_right]; ring)
    simpa only [normalHalfspace,inner_neg_left,neg_nonneg] using h
  apply Subset.antisymm
  · intro x hx
    change 0 ≤ inner (𝕜 := ℝ) (-n) x
    rw [inner_neg_left,neg_nonneg]
    by_contra hh
    have hpos : 0 < inner (𝕜 := ℝ) n x := lt_of_not_ge hh
    have hi : x ∈ interior (normalHalfspace n) := by
      apply mem_interior_iff_mem_nhds.mpr
      have hopen : IsOpen {y : E | (0 : ℝ) < inner (𝕜 := ℝ) n y} :=
        isOpen_lt continuous_const (continuous_const.inner continuous_id)
      apply Filter.mem_of_superset (hopen.mem_nhds hpos)
      intro y hy
      change 0 ≤ inner (𝕜 := ℝ) n y
      exact le_of_lt hy
    exact Set.disjoint_left.mp hdis' hi hx
  · rw [← hneg]
    apply closure_minimal _ hclosed
    intro x hx
    apply (hcover x).resolve_left
    change ¬ 0 ≤ inner (𝕜 := ℝ) n x
    exact not_le.mpr hx

theorem T5_two_incident_opposite_halfspace_germ
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p) (n : R.directionᗮ) (hn : n ≠ 0)
    (hroot : LocalSetEq p (root : Set (Point 5))
      (ridgeNormalProjection R p ⁻¹' normalHalfspace n))
    (hcard : Nat.card (incidentTiles tiles p) = 2) :
    ∃ B : incidentTiles tiles p, B ≠ root ∧
      LocalSetEq p (B : Set (Point 5))
        (ridgeNormalProjection R p ⁻¹' normalHalfspace (-n)) := by
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hshape : HasSectorAngle (normalHalfspace n) Real.pi := .halfplane n hn rfl
  have hrootEq : T5IncidentNormalCone g R p root = normalHalfspace n :=
    normalCones_eq_of_localSetEq R p (hpart.2.2.1 root).2.1 hshape.positive
      ((hpart.2.2.1 root).2.2.symm.trans hroot)
  have hangle : HasSectorAngle (T5IncidentNormalCone g R p root) Real.pi := hrootEq.symm ▸ hshape
  have hboundary := mem_frontier_of_normal_sector R p hpart.2.1 hangle
    Real.pi_pos (by linarith [Real.pi_pos]) (hpart.2.2.1 root).2.2
  have hall := ht.incident_mem_frontier_of_root_sector T5_isCompact R p root hangle
    (hpart.2.2.1 root).2.2 hboundary
  have hinv := T5_generic_incident_sector_inventory ht R hp hcodim g hg hactive hall
  obtain ⟨B,hB⟩ := hpart.2.2.2.1 (-n)
  have hBne : B ≠ root := by
    intro heq
    rw [heq,hrootEq] at hB
    change 0 ≤ inner (𝕜 := ℝ) n (-n) at hB
    rw [inner_neg_right] at hB
    linarith [real_inner_self_pos.mpr hn]
  have htwo : ∀ C : incidentTiles tiles p, C = root ∨ C = B := by
    intro C
    by_cases hC : C = root
    · exact Or.inl hC
    · right
      apply Subtype.ext
      apply IsTiling.companion_eq_of_incident_card_two hcard root.property C.property B.property
      · intro heq; exact hC (Subtype.ext heq)
      · intro heq; exact hBne (Subtype.ext heq)
  obtain ⟨θ,hθ,_⟩ := hinv B
  have heq : T5IncidentNormalCone g R p B = normalHalfspace (-n) :=
    regular_closed_companion_of_halfspace_cover n hn _ (hpart.2.2.1 B).1 hθ.regular_closed
      (by
        intro x
        obtain ⟨C,hC⟩ := hpart.2.2.2.1 x
        rcases htwo C with rfl | rfl
        · exact Or.inl (hrootEq ▸ hC)
        · exact Or.inr hC)
      (by simpa only [← hrootEq] using hpart.2.2.2.2 root B hBne.symm)
  exact ⟨B,hBne,heq ▸ (hpart.2.2.1 B).2.2⟩

#print axioms T5_two_incident_opposite_halfspace_germ

theorem T7_two_incident_opposite_halfspace_germ
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p) (n : R.directionᗮ) (hn : n ≠ 0)
    (hroot : LocalSetEq p (root : Set (Point 7))
      (ridgeNormalProjection R p ⁻¹' normalHalfspace n))
    (hcard : Nat.card (incidentTiles tiles p) = 2) :
    ∃ B : incidentTiles tiles p, B ≠ root ∧
      LocalSetEq p (B : Set (Point 7))
        (ridgeNormalProjection R p ⁻¹' normalHalfspace (-n)) := by
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hshape : HasSectorAngle (normalHalfspace n) Real.pi := .halfplane n hn rfl
  have hrootEq : T7IncidentNormalCone g R p root = normalHalfspace n :=
    normalCones_eq_of_localSetEq R p (hpart.2.2.1 root).2.1 hshape.positive
      ((hpart.2.2.1 root).2.2.symm.trans hroot)
  have hangle : HasSectorAngle (T7IncidentNormalCone g R p root) Real.pi := hrootEq.symm ▸ hshape
  have hboundary := mem_frontier_of_normal_sector R p hpart.2.1 hangle
    Real.pi_pos (by linarith [Real.pi_pos]) (hpart.2.2.1 root).2.2
  have hall := ht.incident_mem_frontier_of_root_sector T7_isCompact R p root hangle
    (hpart.2.2.1 root).2.2 hboundary
  have hinv := T7_generic_incident_sector_inventory ht R hp hcodim g hg hactive hall
  obtain ⟨B,hB⟩ := hpart.2.2.2.1 (-n)
  have hBne : B ≠ root := by
    intro heq
    rw [heq,hrootEq] at hB
    change 0 ≤ inner (𝕜 := ℝ) n (-n) at hB
    rw [inner_neg_right] at hB
    linarith [real_inner_self_pos.mpr hn]
  have htwo : ∀ C : incidentTiles tiles p, C = root ∨ C = B := by
    intro C
    by_cases hC : C = root
    · exact Or.inl hC
    · right
      apply Subtype.ext
      apply IsTiling.companion_eq_of_incident_card_two hcard root.property C.property B.property
      · intro heq; exact hC (Subtype.ext heq)
      · intro heq; exact hBne (Subtype.ext heq)
  obtain ⟨θ,hθ,_⟩ := hinv B
  have heq : T7IncidentNormalCone g R p B = normalHalfspace (-n) :=
    regular_closed_companion_of_halfspace_cover n hn _ (hpart.2.2.1 B).1 hθ.regular_closed
      (by
        intro x
        obtain ⟨C,hC⟩ := hpart.2.2.2.1 x
        rcases htwo C with rfl | rfl
        · exact Or.inl (hrootEq ▸ hC)
        · exact Or.inr hC)
      (by simpa only [← hrootEq] using hpart.2.2.2.2 root B hBne.symm)
  exact ⟨B,hBne,heq ▸ (hpart.2.2.1 B).2.2⟩

#print axioms T7_two_incident_opposite_halfspace_germ

#print axioms regular_closed_companion_of_halfspace_cover
end SparseMonotiles
