module

public import SpectreGeometry.PhysicalEdgeOrientation
public import SpectreGeometry.PhysicalCornerPairs
public import SpectreGeometry.DeformedLatticeCertificate

@[expose] public section


/-! The finite lattice residue restriction is now derived for actual
homochiral physical contacts, rather than supplied as a grid premise.
This is an edgewise development statement, not yet a global deformation. -/
namespace SpectreGeometry
noncomputable section
open Set

theorem relative_frame_eq_opposed (k : Fin 12) (e j : Fin 14)
    (h : directionAdd k (edgeTurn j) = directionAdd (edgeTurn e) 6) :
    k = opposedFrame 0 e j := by
  calc
    k = directionAdd (directionAdd k (edgeTurn j)) (directionInverse (edgeTurn j)) := by
      rw [direction_add_assoc,direction_inverse_right,direction_add_zero]
    _ = directionAdd (directionAdd (edgeTurn e) 6) (directionInverse (edgeTurn j)) := by rw [h]
    _ = opposedFrame 0 e j := by simp only [opposedFrame,direction_zero_add]

theorem opposed_frame_add (r : Fin 12) (e j : Fin 14) :
    directionAdd r (opposedFrame 0 e j) = opposedFrame r e j := by
  simp only [opposedFrame,direction_zero_add,direction_add_assoc]

theorem physical_contact_deformed_anchor_lattice {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (root i : ι) (hij : i ≠ root) (e j : Fin 14)
    (t u : ℝ) (ht : 0 < t) (ht' : t < 1) (hu : 0 < u) (hu' : u < 1)
    (x : EPlane)
    (hxe : x = f root (euclideanCoordinates (interpolate (realVertex e) (realVertex (next e)) t)))
    (hxj : x = f i (euclideanCoordinates (interpolate (realVertex j) (realVertex (next j)) u)))
    (k : Fin 12)
    (hk : ∀ q, coordinateAction (f i) q = coordinateAction (f root) (rotate k q)) :
    ∀ r : Fin 12, InKiteCenterLattice (deformedAnchorShift r (directionAdd r k) e j) := by
  have ho := packing_relative_edge_opposite (f root) (f i) (hdisjoint (Ne.symm hij))
    k hk e j t u ht ht' hu hu' x hxe hxj
  have hke := relative_frame_eq_opposed k e j ho
  obtain ⟨ha,hb⟩ := homochiral_contact_unit_edges_reversed f hdirect hdisjoint hcover
    root i hij e j t u ht ht' hu hu' x hxe hxj
  have hall := physical_reversed_edge_pair_allowed f hdirect hdisjoint hcover root i hij e j ha hb
  intro r
  rw [hke,opposed_frame_add]
  exact deformed_anchor_shift_lattice r e j hall

end
end SpectreGeometry
