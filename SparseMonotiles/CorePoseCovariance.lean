module

public import SparseMonotiles.ContactPhysicalOverlapTiles

@[expose] public section

/-! Full open integer-cell cores commute with the exact signed lower-cell
pose action. This supplies the whole-core coverage needed by global clamping;
it does not substitute a separated family of small balls. -/
namespace SparseMonotiles.Contact
open Set

theorem Pose.euclidean_mem_integerCellCore {d : ℕ} (p : Pose d)
    (mu : ℚ) (c : Cell d) (x : Point d) :
    p.euclidean x ∈ integerCellCore mu (p.cell c) ↔ x ∈ integerCellCore mu c := by
  constructor
  · intro hx j
    obtain ⟨i,rfl⟩ := p.perm.surjective j
    have hi := hx i
    rw [Pose.euclidean_apply] at hi
    cases hn : p.negative i <;> simp [Pose.cell,Pose.sign,hn] at hi <;>
      constructor <;> linarith
  · intro hx i
    have hi := hx (p.perm i)
    rw [Pose.euclidean_apply]
    cases hn : p.negative i <;> simp [Pose.cell,Pose.sign,hn] <;>
      constructor <;> linarith [hi.1,hi.2]

theorem Pose.image_integerCellCore {d : ℕ} (p : Pose d) (mu : ℚ) (c : Cell d) :
    p.euclidean '' integerCellCore mu c = integerCellCore mu (p.cell c) := by
  ext y
  obtain ⟨x,rfl⟩ := p.euclidean.surjective y
  constructor
  · rintro ⟨z,hz,he⟩
    have hzx : z=x := p.euclidean.injective he
    subst z
    exact (p.euclidean_mem_integerCellCore mu c x).mpr hz
  · intro hx
    exact ⟨x,(p.euclidean_mem_integerCellCore mu c x).mp hx,rfl⟩

theorem occupied_core_subset_posed_interior {d : ℕ} {T : Set (Point d)}
    (mu : ℚ)
    (cores : ∀ bits : Fin d → Bool, (∃ i, bits i=false) →
      carrierCellCore mu bits ⊆ interior T)
    (p : Pose d) (c : Cell d) (hc : IsChairCell (p.inverseCell c)) :
    integerCellCore mu c ⊆ interior (p.euclidean '' T) := by
  obtain ⟨bits,hbits,hcEq⟩ := exists_binaryCell_of_isChairCell hc
  have hsource : integerCellCore mu (p.inverseCell c) ⊆ interior T := by
    rw [← hcEq]
    exact cores bits hbits
  have h := Set.image_mono hsource (f := (p.euclidean : Point d → Point d))
  rw [p.image_integerCellCore,Pose.cell_inverseCell] at h
  rw [show (p.euclidean : Point d → Point d) = p.euclidean.toHomeomorph from rfl,
    p.euclidean.toHomeomorph.image_interior] at h
  exact h

theorem T5_occupied_core_subset_posed_interior (p : Pose 5) (c : Cell 5)
    (hc : IsChairCell (p.inverseCell c)) :
    integerCellCore (1/100) c ⊆ interior (p.euclidean '' T5) :=
  occupied_core_subset_posed_interior (1/100) T5_carrierCellCore_subset_interior p c hc

theorem T7_occupied_core_subset_posed_interior (p : Pose 7) (c : Cell 7)
    (hc : IsChairCell (p.inverseCell c)) :
    integerCellCore (1/100) c ⊆ interior (p.euclidean '' T7) :=
  occupied_core_subset_posed_interior (1/100) T7_carrierCellCore_subset_interior p c hc

#print axioms Pose.image_integerCellCore
#print axioms T5_occupied_core_subset_posed_interior
#print axioms T7_occupied_core_subset_posed_interior
end SparseMonotiles.Contact
