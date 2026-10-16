module

public import SpectreGeometry.CornerSignData

@[expose] public section


namespace SpectreGeometry

def edgeSector (i : Fin 14) (d : Fin 12) : Prop :=
  Quad3.positive (ExactPoint.det (edge i) (sectorVector d))
instance (i : Fin 14) (d : Fin 12) : Decidable (edgeSector i d) := inferInstanceAs (Decidable (Quad3.positive _))
def edgeSectorList (i : Fin 14) : List (Fin 12) := (List.finRange 12).filter (fun d => decide (edgeSector i d))
theorem edge_sector_count : ∀ i : Fin 14, (edgeSectorList i).length = 6 := by decide

abbrev BoundarySlot := Sum (Fin 14) (Fin 14)
def slotSector (b : BoundarySlot) (d : Fin 12) : Prop :=
  match b with | .inl i => cornerSector i d | .inr i => edgeSector i d
instance (b : BoundarySlot) (d : Fin 12) : Decidable (slotSector b d) := by
  cases b <;> dsimp [slotSector] <;> infer_instance
def slotSectorList (b : BoundarySlot) : List (Fin 12) :=
  (List.finRange 12).filter (fun d => decide (slotSector b d))
theorem slot_sector_minimum : ∀ b : BoundarySlot, 3 ≤ (slotSectorList b).length := by
  intro b
  cases b with
  | inl i =>
      change 3 ≤ (cornerSectorList i).length
      rw [corner_sector_count]
      exact corner_steps_minimum i
  | inr i =>
      change 3 ≤ (edgeSectorList i).length
      rw [edge_sector_count]
      decide
theorem slot_sector_sizes : ∀ b : BoundarySlot,
    (slotSectorList b).length = 3 ∨ (slotSectorList b).length = 4 ∨
    (slotSectorList b).length = 6 ∨ (slotSectorList b).length = 8 ∨
    (slotSectorList b).length = 9 := by
  intro b
  cases b with
  | inl i =>
      change (cornerSectorList i).length = 3 ∨ (cornerSectorList i).length = 4 ∨
        (cornerSectorList i).length = 6 ∨ (cornerSectorList i).length = 8 ∨ (cornerSectorList i).length = 9
      rw [corner_sector_count]
      exact corner_steps_values i
  | inr i =>
      change (edgeSectorList i).length = 3 ∨ (edgeSectorList i).length = 4 ∨
        (edgeSectorList i).length = 6 ∨ (edgeSectorList i).length = 8 ∨ (edgeSectorList i).length = 9
      rw [edge_sector_count]
      exact Or.inr (Or.inr (Or.inl rfl))

end SpectreGeometry
