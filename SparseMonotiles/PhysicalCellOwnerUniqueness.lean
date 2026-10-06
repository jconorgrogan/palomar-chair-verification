module

public import SparseMonotiles.RegisteredPhysicalWorld

@[expose] public section

/-! An occupied integer cell has only one actual physical owner, even when
registration is known only for the two tiles being compared. -/
namespace SparseMonotiles
open Set Contact

theorem physical_tiles_eq_of_shared_registered_cell {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))} (ht : IsTiling T tiles)
    (hi : ∀ c : Cell d, IsChairCell c → cellCentre c ∈ interior T)
    (g : tiles → Point d ≃ᵢ Point d)
    (hg : ∀ A : tiles, (A : Set (Point d))=g A '' T)
    (e : Point d ≃ᵢ Point d) (B C : tiles) (p q : Pose d)
    (hp : (g B).trans e=p.euclidean.toIsometryEquiv)
    (hq : (g C).trans e=q.euclidean.toIsometryEquiv)
    (c : Cell d) (hcB : IsChairCell (p.inverseCell c))
    (hcC : IsChairCell (q.inverseCell c)) : B=C := by
  have himage : ∀ (A : tiles) (s : Pose d),
      (g A).trans e=s.euclidean.toIsometryEquiv →
      e '' (A : Set (Point d))=s.euclidean '' T := by
    intro A s hs
    calc
      e '' (A : Set (Point d)) = e '' (g A '' T) := congrArg (fun S => e '' S) (hg A)
      _ = ((g A).trans e) '' T := image_image e (g A) T
      _ = s.euclidean '' T := by rw [hs]; rfl
  have hp' := posed_cellCentre_mem_interior hi p c hcB
  have hq' := posed_cellCentre_mem_interior hi q c hcC
  rw [← himage B p hp] at hp'
  rw [← himage C q hq] at hq'
  have hxB : e.symm (cellCentre c) ∈ interior (B : Set (Point d)) := by
    rw [show (e : Point d → Point d)=e.toHomeomorph from rfl,
      ← e.toHomeomorph.image_interior] at hp'
    rcases hp' with ⟨x,hx,he⟩
    simpa [← he] using hx
  have hxC : e.symm (cellCentre c) ∈ interior (C : Set (Point d)) := by
    rw [show (e : Point d → Point d)=e.toHomeomorph from rfl,
      ← e.toHomeomorph.image_interior] at hq'
    rcases hq' with ⟨x,hx,he⟩
    simpa [← he] using hx
  apply Subtype.ext
  by_cases he : (B : Set (Point d))=(C : Set (Point d))
  · exact he
  · exact False.elim (Set.disjoint_left.mp (ht.2.2 B B.property C C.property he) hxB hxC)

theorem T5_physical_tiles_eq_of_shared_registered_cell
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5))=g A '' T5)
    (A B C : tiles) (p q : Pose 5)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (hq : (g C).trans (g A).symm=q.euclidean.toIsometryEquiv)
    (c : Cell 5) (hcB : IsChairCell (p.inverseCell c))
    (hcC : IsChairCell (q.inverseCell c)) : B=C :=
  physical_tiles_eq_of_shared_registered_cell ht (fun _ hc => T5_cellCentre_mem_interior hc)
    g hg (g A).symm B C p q hp hq c hcB hcC

theorem T7_physical_tiles_eq_of_shared_registered_cell
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7))=g A '' T7)
    (A B C : tiles) (p q : Pose 7)
    (hp : (g B).trans (g A).symm=p.euclidean.toIsometryEquiv)
    (hq : (g C).trans (g A).symm=q.euclidean.toIsometryEquiv)
    (c : Cell 7) (hcB : IsChairCell (p.inverseCell c))
    (hcC : IsChairCell (q.inverseCell c)) : B=C :=
  physical_tiles_eq_of_shared_registered_cell ht (fun _ hc => T7_cellCentre_mem_interior hc)
    g hg (g A).symm B C p q hp hq c hcB hcC

#print axioms physical_tiles_eq_of_shared_registered_cell
#print axioms T5_physical_tiles_eq_of_shared_registered_cell
#print axioms T7_physical_tiles_eq_of_shared_registered_cell
end SparseMonotiles
