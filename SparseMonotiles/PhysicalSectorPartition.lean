module

public import SparseMonotiles.KeyRidgeAngles
public import SparseMonotiles.PhysicalNormalConePartition
public import SparseMonotiles.PhysicalSectorBoundary
public import SparseMonotiles.SectorAngleSumArithmetic

@[expose] public section

/-! # Actual incident sector partitions for the exact T5/T7 bodies
All incident indices are retained. The angle inventory comes from the literal
body geometry and the angle sum comes from the genuine normal-cone partition.
Only the distinguished root's local sector and boundary status are supplied.
-/
namespace SparseMonotiles
open Set
open scoped BigOperators

/-- Every boundary tile in the actual incident family has a geometric sector
angle in the proved literal-body inventory. -/
theorem T5_generic_incident_sector_inventory
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (hboundary : ∀ A : incidentTiles tiles p, p ∈ frontier (A : Set (Point 5))) :
    ∀ A : incidentTiles tiles p, ∃ θ,
      SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p A) θ ∧
      SectorArithmetic.InAngleInventory θ := by
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  intro A
  have hEq := hg ⟨A,A.property.1⟩
  apply T5_boundary_normal_cone_sector_inventory (g ⟨A,A.property.1⟩) R hp hcodim
    (hactive A) (hpart.2.2.1 A).2.1
  · simpa only [← hEq] using (hpart.2.2.1 A).2.2
  · simpa only [← hEq] using hboundary A

/-- The actual finite family has total angle 2π. Boundary status of every
other tile is derived from the genuine root sector and disjoint interiors. -/
theorem T5_generic_root_sector_partition
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p) {θ : ℝ}
    (hroot : SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p root) θ)
    (hrootInv : SectorArithmetic.InAngleInventory θ)
    (hboundary : p ∈ frontier (root : Set (Point 5))) :
    ∃ width : incidentTiles tiles p → ℝ,
      width root = θ ∧
      (∀ A, SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p A) (width A)) ∧
      (∀ A, SectorArithmetic.InAngleInventory (width A)) ∧
      (∑' A, width A) = 2*Real.pi := by
  classical
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  letI : Fintype (incidentTiles tiles p) := hpart.1.fintype
  have hall := ht.incident_mem_frontier_of_root_sector T5_isCompact R p root hroot
    (hpart.2.2.1 root).2.2 hboundary
  have hinv := T5_generic_incident_sector_inventory ht R hp hcodim g hg hactive hall
  let width : incidentTiles tiles p → ℝ := fun A =>
    if A = root then θ else Classical.choose (hinv A)
  have hwidthroot : width root = θ := by simp [width]
  have hshape (A : incidentTiles tiles p) :
      SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p A) (width A) := by
    by_cases hA : A = root
    · simpa [width,hA] using hroot
    · simpa only [width,if_neg hA] using (Classical.choose_spec (hinv A)).1
  have hwInv (A : incidentTiles tiles p) : SectorArithmetic.InAngleInventory (width A) := by
    by_cases hA : A = root
    · simpa [width,hA] using hrootInv
    · simpa only [width,if_neg hA] using (Classical.choose_spec (hinv A)).2
  refine ⟨width,hwidthroot,hshape,hwInv,?_⟩
  rw [tsum_fintype]
  exact SectorAngleSum.rank_two_geometric_sector_partition_sum hpart.2.1
    (T5IncidentNormalCone g R p) width hshape hpart.2.2.2.1 hpart.2.2.2.2

#print axioms T5_generic_incident_sector_inventory
#print axioms T5_generic_root_sector_partition

/-- Every boundary tile in the actual incident family has a geometric sector
angle in the proved literal-body inventory. -/
theorem T7_generic_incident_sector_inventory
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (hboundary : ∀ A : incidentTiles tiles p, p ∈ frontier (A : Set (Point 7))) :
    ∀ A : incidentTiles tiles p, ∃ θ,
      SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p A) θ ∧
      SectorArithmetic.InAngleInventory θ := by
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  intro A
  have hEq := hg ⟨A,A.property.1⟩
  apply T7_boundary_normal_cone_sector_inventory (g ⟨A,A.property.1⟩) R hp hcodim
    (hactive A) (hpart.2.2.1 A).2.1
  · simpa only [← hEq] using (hpart.2.2.1 A).2.2
  · simpa only [← hEq] using hboundary A

/-- The actual finite family has total angle 2π. Boundary status of every
other tile is derived from the genuine root sector and disjoint interiors. -/
theorem T7_generic_root_sector_partition
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p) {θ : ℝ}
    (hroot : SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p root) θ)
    (hrootInv : SectorArithmetic.InAngleInventory θ)
    (hboundary : p ∈ frontier (root : Set (Point 7))) :
    ∃ width : incidentTiles tiles p → ℝ,
      width root = θ ∧
      (∀ A, SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p A) (width A)) ∧
      (∀ A, SectorArithmetic.InAngleInventory (width A)) ∧
      (∑' A, width A) = 2*Real.pi := by
  classical
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  letI : Fintype (incidentTiles tiles p) := hpart.1.fintype
  have hall := ht.incident_mem_frontier_of_root_sector T7_isCompact R p root hroot
    (hpart.2.2.1 root).2.2 hboundary
  have hinv := T7_generic_incident_sector_inventory ht R hp hcodim g hg hactive hall
  let width : incidentTiles tiles p → ℝ := fun A =>
    if A = root then θ else Classical.choose (hinv A)
  have hwidthroot : width root = θ := by simp [width]
  have hshape (A : incidentTiles tiles p) :
      SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p A) (width A) := by
    by_cases hA : A = root
    · simpa [width,hA] using hroot
    · simpa only [width,if_neg hA] using (Classical.choose_spec (hinv A)).1
  have hwInv (A : incidentTiles tiles p) : SectorArithmetic.InAngleInventory (width A) := by
    by_cases hA : A = root
    · simpa [width,hA] using hrootInv
    · simpa only [width,if_neg hA] using (Classical.choose_spec (hinv A)).2
  refine ⟨width,hwidthroot,hshape,hwInv,?_⟩
  rw [tsum_fintype]
  exact SectorAngleSum.rank_two_geometric_sector_partition_sum hpart.2.1
    (T7IncidentNormalCone g R p) width hshape hpart.2.2.2.1 hpart.2.2.2.2

#print axioms T7_generic_incident_sector_inventory
#print axioms T7_generic_root_sector_partition


/-- K2's companion count for the full actual incident family. Its inventory
and complementary sum are derived from the exact physical tiling. -/
theorem T5_generic_key_root_exactly_two_incident
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p) {θ δ : ℝ}
    (hroot : SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p root) θ)
    (hδ : 0 < δ) (hδ' : δ < Real.pi/4)
    (hkey : θ = Real.pi-δ ∨ θ = Real.pi+δ)
    (hboundary : p ∈ frontier (root : Set (Point 5))) :
    Nat.card (incidentTiles tiles p) = 2 := by
  classical
  have hinv : SectorArithmetic.InAngleInventory θ :=
    Or.inr (Or.inr (Or.inr ⟨δ,hδ,hδ',hkey⟩))
  obtain ⟨width,hwroot,hshape,hInv,_⟩ := T5_generic_root_sector_partition
    ht R hp hcodim g hg hactive root hroot hinv hboundary
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  letI : Fintype (incidentTiles tiles p) := hpart.1.fintype
  have hk : width root = Real.pi-δ ∨ width root = Real.pi+δ := by
    rw [hwroot]
    exact hkey
  have hc := SectorAngleSum.key_sector_unique_companion hpart.2.1
    (T5IncidentNormalCone g R p) width hshape hpart.2.2.2.1 hpart.2.2.2.2
    root hδ hδ' hk (fun A _ => hInv A)
  simpa only [Nat.card_eq_fintype_card] using hc.2.2

/-- The full actual incident count at a flat root is two or three. The
geometric exclusion of the two-right-angle seam is a further K1 obligation. -/
theorem T5_generic_flat_root_incident_count
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p)
    (hroot : SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p root) Real.pi)
    (hboundary : p ∈ frontier (root : Set (Point 5))) :
    Nat.card (incidentTiles tiles p) = 2 ∨ Nat.card (incidentTiles tiles p) = 3 := by
  classical
  obtain ⟨width,hwroot,hshape,hInv,_⟩ := T5_generic_root_sector_partition
    ht R hp hcodim g hg hactive root hroot (Or.inr (Or.inl rfl)) hboundary
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  letI : Fintype (incidentTiles tiles p) := hpart.1.fintype
  have hc := SectorAngleSum.flat_sector_companions hpart.2.1
    (T5IncidentNormalCone g R p) width hshape hpart.2.2.2.1 hpart.2.2.2.2
    root hwroot (fun A _ => hInv A)
  have hlen := SectorAngleSum.companionAngles_length width root
  rw [Nat.card_eq_fintype_card]
  rcases hc with hc | hc
  · rw [hc] at hlen
    simp only [List.length_singleton] at hlen
    omega
  · rw [hc] at hlen
    simp only [List.length_cons,List.length_nil] at hlen
    omega

#print axioms T5_generic_key_root_exactly_two_incident
#print axioms T5_generic_flat_root_incident_count

/-- K2's companion count for the full actual incident family. Its inventory
and complementary sum are derived from the exact physical tiling. -/
theorem T7_generic_key_root_exactly_two_incident
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p) {θ δ : ℝ}
    (hroot : SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p root) θ)
    (hδ : 0 < δ) (hδ' : δ < Real.pi/4)
    (hkey : θ = Real.pi-δ ∨ θ = Real.pi+δ)
    (hboundary : p ∈ frontier (root : Set (Point 7))) :
    Nat.card (incidentTiles tiles p) = 2 := by
  classical
  have hinv : SectorArithmetic.InAngleInventory θ :=
    Or.inr (Or.inr (Or.inr ⟨δ,hδ,hδ',hkey⟩))
  obtain ⟨width,hwroot,hshape,hInv,_⟩ := T7_generic_root_sector_partition
    ht R hp hcodim g hg hactive root hroot hinv hboundary
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  letI : Fintype (incidentTiles tiles p) := hpart.1.fintype
  have hk : width root = Real.pi-δ ∨ width root = Real.pi+δ := by
    rw [hwroot]
    exact hkey
  have hc := SectorAngleSum.key_sector_unique_companion hpart.2.1
    (T7IncidentNormalCone g R p) width hshape hpart.2.2.2.1 hpart.2.2.2.2
    root hδ hδ' hk (fun A _ => hInv A)
  simpa only [Nat.card_eq_fintype_card] using hc.2.2

/-- The full actual incident count at a flat root is two or three. The
geometric exclusion of the two-right-angle seam is a further K1 obligation. -/
theorem T7_generic_flat_root_incident_count
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root : incidentTiles tiles p)
    (hroot : SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p root) Real.pi)
    (hboundary : p ∈ frontier (root : Set (Point 7))) :
    Nat.card (incidentTiles tiles p) = 2 ∨ Nat.card (incidentTiles tiles p) = 3 := by
  classical
  obtain ⟨width,hwroot,hshape,hInv,_⟩ := T7_generic_root_sector_partition
    ht R hp hcodim g hg hactive root hroot (Or.inr (Or.inl rfl)) hboundary
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  letI : Fintype (incidentTiles tiles p) := hpart.1.fintype
  have hc := SectorAngleSum.flat_sector_companions hpart.2.1
    (T7IncidentNormalCone g R p) width hshape hpart.2.2.2.1 hpart.2.2.2.2
    root hwroot (fun A _ => hInv A)
  have hlen := SectorAngleSum.companionAngles_length width root
  rw [Nat.card_eq_fintype_card]
  rcases hc with hc | hc
  · rw [hc] at hlen
    simp only [List.length_singleton] at hlen
    omega
  · rw [hc] at hlen
    simp only [List.length_cons,List.length_nil] at hlen
    omega

#print axioms T7_generic_key_root_exactly_two_incident
#print axioms T7_generic_flat_root_incident_count

end SparseMonotiles
