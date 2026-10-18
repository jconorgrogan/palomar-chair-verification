module

public import SpectreGeometry.EdgeSectorData

@[expose] public section


/-! Literal direction certificates for boundary rays of the exact masks.
These do not by themselves imply any physical registration. -/
namespace SpectreGeometry

def slotInitialDirection (b : BoundarySlot) : Fin 12 :=
  match b with | .inl i => edgeTurn i | .inr i => edgeTurn i

def slotFinalDirection (b : BoundarySlot) : Fin 12 :=
  match b with
  | .inl i => directionAdd (edgeTurn (previous i)) 6
  | .inr i => directionAdd (edgeTurn i) 6

theorem slot_sector_initial_ray : ∀ (b : BoundarySlot) (d : Fin 12),
    slotSector b d → ¬slotSector b (directionAdd d 11) → d = slotInitialDirection b := by
  intro b
  cases b with
  | inl i => revert i; decide
  | inr i => revert i; decide

theorem slot_sector_final_ray : ∀ (b : BoundarySlot) (d : Fin 12),
    slotSector b d → ¬slotSector b (directionAdd d 1) → directionAdd d 1 = slotFinalDirection b := by
  intro b
  cases b with
  | inl i => revert i; decide
  | inr i => revert i; decide

theorem edge_sector_boundary_samples : ∀ e : Fin 14,
    edgeSector e (directionAdd (edgeTurn e) 5) ∧
    edgeSector e (edgeTurn e) ∧
    ¬edgeSector e (directionAdd (edgeTurn e) 6) ∧
    ¬edgeSector e (directionAdd (edgeTurn e) 11) := by decide

theorem edge_endpoint_not_both_small : ∀ e : Fin 14,
    ¬ ((cornerSteps e = 3 ∨ cornerSteps e = 6) ∧
       (cornerSteps (next e) = 3 ∨ cornerSteps (next e) = 6)) := by decide

end SpectreGeometry
