module

public import SparseMonotiles.Tile5BoundaryFacts
public import SparseMonotiles.Tile7BoundaryFacts
public import SparseMonotiles.CarrierFacetHalfspace
public import SparseMonotiles.PhysicalSectorPartition

@[expose] public section

/-!
# The actual flat-neighbor contradiction at a key crease

The literal clearance bounds make the edge strip a genuine flat boundary
patch, even before registration of arbitrary placed tiles. At a generic key
crease, the complete physical incident family cannot include a distinct flat
sector. The proof uses its derived geometric partition, retaining all actual
incident indices. No companion uniqueness is a hypothesis.
-/
namespace SparseMonotiles
open Set Filter
open scoped Topology

/-- Every point of an exposed carrier facet strictly within quarter distance
of an integer-skeleton point has the exact physical halfspace germ. -/
theorem T5_facet_halfspace_near_skeleton (f : Contact.Facet 5)
    (howner : Contact.IsChairCell f.cell) (hexposed : ¬ Contact.IsChairCell f.neighbor)
    {p z : Point 5} (hp : p ∈ f.relativeInterior) (hz : z ∈ integerSkeleton 5)
    (hdist : dist p z < 1/4) : LocalSetEq p T5 f.inwardHalfspace := by
  have haway : ∀ᶠ x in 𝓝 p, ∀ k ∈ keys5, x ∉ keySolid k := by
    apply Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hdist)
    intro x hx
    exact T5_keys_avoid_skeleton_quarter_ball hz x (Metric.ball_subset_closedBall hx)
  exact (localSetEq_body_carrier_away_keys haway).trans
    (f.localSetEq_carrier_inwardHalfspace_of_relativeInterior howner hexposed hp)

/-- The seven-dimensional literal body has the same key-free edge strip. -/
theorem T7_facet_halfspace_near_skeleton (f : Contact.Facet 7)
    (howner : Contact.IsChairCell f.cell) (hexposed : ¬ Contact.IsChairCell f.neighbor)
    {p z : Point 7} (hp : p ∈ f.relativeInterior) (hz : z ∈ integerSkeleton 7)
    (hdist : dist p z < 1/4) : LocalSetEq p T7 f.inwardHalfspace := by
  have haway : ∀ᶠ x in 𝓝 p, ∀ k ∈ keys7, x ∉ keySolid k := by
    apply Filter.Eventually.mono (Metric.isOpen_ball.mem_nhds hdist)
    intro x hx
    exact T7_keys_avoid_skeleton_quarter_ball hz x (Metric.ball_subset_closedBall hx)
  exact (localSetEq_body_carrier_away_keys haway).trans
    (f.localSetEq_carrier_inwardHalfspace_of_relativeInterior howner hexposed hp)

/-- Arbitrary rotations, translations, and reflections preserve the flat strip. -/
theorem T5_copy_facet_halfspace_near_skeleton (g : Point 5 ≃ᵢ Point 5)
    (f : Contact.Facet 5) (howner : Contact.IsChairCell f.cell)
    (hexposed : ¬ Contact.IsChairCell f.neighbor)
    {p z : Point 5} (hp : p ∈ f.relativeInterior) (hz : z ∈ integerSkeleton 5)
    (hdist : dist p z < 1/4) :
    LocalSetEq (g p) (g '' T5) (g '' f.inwardHalfspace) :=
  (T5_facet_halfspace_near_skeleton f howner hexposed hp hz hdist).image_isometry g

/-- The same unregistered-isometry transport in dimension seven. -/
theorem T7_copy_facet_halfspace_near_skeleton (g : Point 7 ≃ᵢ Point 7)
    (f : Contact.Facet 7) (howner : Contact.IsChairCell f.cell)
    (hexposed : ¬ Contact.IsChairCell f.neighbor)
    {p z : Point 7} (hp : p ∈ f.relativeInterior) (hz : z ∈ integerSkeleton 7)
    (hdist : dist p z < 1/4) :
    LocalSetEq (g p) (g '' T7) (g '' f.inwardHalfspace) :=
  (T7_facet_halfspace_near_skeleton f howner hexposed hp hz hdist).image_isometry g

namespace SectorAngleSum

/-- A genuine geometric key sector has no distinct flat companion. The
angle inventory concerns all actual indices, and the angle sum is derived
from the geometric partition. In particular no face-to-face or companion
uniqueness premise appears here. -/
theorem key_sector_no_flat_companion
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
    (hdim : Module.finrank ℝ E = 2) (sector : ι → Set E) (width : ι → ℝ)
    (hshape : ∀ i, HasSectorAngle (sector i) (width i))
    (hcover : ∀ v : E, ∃ i, v ∈ sector i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (sector i)) (interior (sector j))))
    (root flat : ι) (hne : flat ≠ root)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < Real.pi/4)
    (hkey : width root = Real.pi-δ ∨ width root = Real.pi+δ)
    (hinv : ∀ i, SectorArithmetic.InAngleInventory (width i))
    (hflat : HasSectorAngle (sector flat) Real.pi) : False := by
  let w : ι → ℝ := fun i => if i = flat then Real.pi else width i
  have hwroot : w root = width root := by simp [w,Ne.symm hne]
  have hwshape (i : ι) : HasSectorAngle (sector i) (w i) := by
    by_cases hi : i = flat
    · simpa [w,hi] using hflat
    · simpa [w,hi] using hshape i
  have hwinv (i : ι) : SectorArithmetic.InAngleInventory (w i) := by
    by_cases hi : i = flat
    · simp only [w,if_pos hi]
      exact Or.inr (Or.inl rfl)
    · simpa [w,hi] using hinv i
  obtain ⟨hc,hnonflat,_⟩ := key_sector_unique_companion hdim sector w hwshape
    hcover hdisjoint root hδ hδ' (by simpa [hwroot] using hkey) (fun i _ => hwinv i)
  have hm : Real.pi ∈ companionAngles w root :=
    (mem_companionAngles w root Real.pi).mpr ⟨flat,hne,by simp [w]⟩
  rw [hc,List.mem_singleton] at hm
  exact hnonflat hm.symm

end SectorAngleSum

/-- The exact T5 tiling cannot have a distinct flat tile at a generic key
crease. The full incident inventory and covering sectors are proved from the
literal physical body. -/
theorem T5_generic_key_root_no_flat_incident
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root flat : incidentTiles tiles p) (hne : flat ≠ root) {θ δ : ℝ}
    (hroot : SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p root) θ)
    (hδ : 0 < δ) (hδ' : δ < Real.pi/4)
    (hkey : θ = Real.pi-δ ∨ θ = Real.pi+δ)
    (hboundary : p ∈ frontier (root : Set (Point 5)))
    (hflat : SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p flat) Real.pi) :
    False := by
  classical
  have hinv : SectorArithmetic.InAngleInventory θ :=
    Or.inr (Or.inr (Or.inr ⟨δ,hδ,hδ',hkey⟩))
  obtain ⟨width,hwroot,hshape,hInv,_⟩ := T5_generic_root_sector_partition
    ht R hp hcodim g hg hactive root hroot hinv hboundary
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  letI : Fintype (incidentTiles tiles p) := hpart.1.fintype
  exact SectorAngleSum.key_sector_no_flat_companion hpart.2.1
    (T5IncidentNormalCone g R p) width hshape hpart.2.2.2.1 hpart.2.2.2.2 root flat hne
    hδ hδ' (by simpa [hwroot] using hkey) hInv hflat

/-- The exact T7 tiling cannot have a distinct flat tile at a generic key
crease. The full incident inventory and covering sectors are proved from the
literal physical body. -/
theorem T7_generic_key_root_no_flat_incident
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root flat : incidentTiles tiles p) (hne : flat ≠ root) {θ δ : ℝ}
    (hroot : SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p root) θ)
    (hδ : 0 < δ) (hδ' : δ < Real.pi/4)
    (hkey : θ = Real.pi-δ ∨ θ = Real.pi+δ)
    (hboundary : p ∈ frontier (root : Set (Point 7)))
    (hflat : SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p flat) Real.pi) :
    False := by
  classical
  have hinv : SectorArithmetic.InAngleInventory θ :=
    Or.inr (Or.inr (Or.inr ⟨δ,hδ,hδ',hkey⟩))
  obtain ⟨width,hwroot,hshape,hInv,_⟩ := T7_generic_root_sector_partition
    ht R hp hcodim g hg hactive root hroot hinv hboundary
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  letI : Fintype (incidentTiles tiles p) := hpart.1.fintype
  exact SectorAngleSum.key_sector_no_flat_companion hpart.2.1
    (T7IncidentNormalCone g R p) width hshape hpart.2.2.2.1 hpart.2.2.2.2 root flat hne
    hδ hδ' (by simpa [hwroot] using hkey) hInv hflat

#print axioms T5_facet_halfspace_near_skeleton
#print axioms T7_facet_halfspace_near_skeleton
#print axioms T5_copy_facet_halfspace_near_skeleton
#print axioms T7_copy_facet_halfspace_near_skeleton
#print axioms SectorAngleSum.key_sector_no_flat_companion
#print axioms T5_generic_key_root_no_flat_incident
#print axioms T7_generic_key_root_no_flat_incident
end SparseMonotiles
