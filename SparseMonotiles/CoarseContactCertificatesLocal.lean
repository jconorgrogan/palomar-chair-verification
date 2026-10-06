module

public import SparseMonotiles.CarrierHierarchyCoarseChecker

@[expose] public section

/-!
Local necessity for one disjoint, touching pair of canonical parent patches.
The statement concerns undecorated carriers and explicitly assumes alignment
and every canonical cross-child contact is legal. In an actual physical-quotient
world, the separately proved alignment and gauge-closure bridges supply these
premises; no global selection of framed222-language representatives is used.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def CanonicalCrossLegal {d : ℕ} (C : Finset (Pose d)) (L : Set (Pose d))
    (F : Pose d) : Prop := ∀ a ∈ C, ∀ b ∈ C,
  CellContact a (compose F b) → normalize a (compose F b) ∈ L

/-- An actual parent unit-face contact supplies a legal canonical child witness.
This is an exhaustive geometric-to-generator bridge, not a bounded search. -/
theorem local_parent_candidate {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    (C : Finset (Pose d)) (L : Set (Pose d)) (hC : CoversCanonicalChildren σ C)
    (F : Pose d) (hlegal : CanonicalCrossLegal C L F)
    {x y : Cell d} (hx : ParentOccupies (rootPose d) x) (hy : ParentOccupies F y)
    (hadj : AdjacentCells x y) :
    ∃ a ∈ C, ∃ b ∈ C, ∃ k ∈ L, F = parentCandidate a b k := by
  obtain ⟨s, hs, hsx⟩ := (parent_support_dissection σ (rootPose d) x).mp hx
  obtain ⟨t, ht, hty⟩ := (parent_support_dissection σ F y).mp hy
  obtain ⟨a, ha, rfl⟩ := canonical_child_form hC (rootPose d) hs
  obtain ⟨b, hb, rfl⟩ := canonical_child_form hC F ht
  rw [compose_root_left] at hsx
  have hk := hlegal a ha b hb ⟨x, y, hsx, hty, hadj⟩
  refine ⟨a, ha, b, hb, normalize a (compose F b), hk, ?_⟩
  have hroot : normalize (rootPose d) F = F := by
    simpa only [compose_root_left] using compose_normalize (rootPose d) F
  simpa only [compose_root_left, hroot] using parent_witness_reconstruction (rootPose d) F a b

/-- Each finite rejection witness contradicts the explicit local pair premises. -/
theorem CoarseWitness.local_sound {d : ℕ} (C : Finset (Pose d)) (L : Set (Pose d))
    (F : Pose d)
    (hdisjoint : ∀ x, ¬ (ParentOccupies (rootPose d) x ∧ ParentOccupies F x))
    (hlegal : CanonicalCrossLegal C L F) {w : CoarseWitness d}
    (hw : w.Valid C L F) : coarsePose (fun _ => 0) F ∈ L := by
  cases w with
  | member => exact hw
  | overlap x => exact False.elim (hdisjoint x hw)
  | illegalChild a b x y =>
      obtain ⟨ha, hb, hax, hby, hadj, hbad⟩ := hw
      exact False.elim (hbad (hlegal a ha b hb ⟨x, y, hax, hby, hadj⟩))

/-- Certificate-backed necessity for every disjoint touching aligned parent pair. -/
theorem indexed_local_coarse_certificate {d : ℕ} {ρ : Type}
    {σ : Bits d → Equiv.Perm (Fin d)}
    (C : Finset (Pose d)) (L : Set (Pose d)) (hC : CoversCanonicalChildren σ C)
    (rows : ρ → CoarseRow d)
    (valid : ∀ i, (rows i).witness.Valid C L (rows i).pose)
    (covered : ∀ a ∈ C, ∀ b ∈ C, ∀ k ∈ L,
      (∀ j, (parentCandidate a b k).shift j % 2 = 0) →
      ∃ i, parentCandidate a b k = (rows i).pose)
    (F : Pose d) (heven : ∀ i, F.shift i % 2 = 0)
    (hdisjoint : ∀ x, ¬ (ParentOccupies (rootPose d) x ∧ ParentOccupies F x))
    (hlegal : CanonicalCrossLegal C L F)
    {x y : Cell d} (hx : ParentOccupies (rootPose d) x) (hy : ParentOccupies F y)
    (hadj : AdjacentCells x y) : coarsePose (fun _ => 0) F ∈ L := by
  obtain ⟨a, ha, b, hb, k, hk, hF⟩ := local_parent_candidate C L hC F hlegal hx hy hadj
  have hEven : ∀ j, (parentCandidate a b k).shift j % 2 = 0 := by simpa [← hF] using heven
  obtain ⟨i, hi⟩ := covered a ha b hb k hk hEven
  have hv : (rows i).witness.Valid C L F := by
    rw [hF, hi]
    exact valid i
  exact CoarseWitness.local_sound C L F hdisjoint hlegal hv

#print axioms local_parent_candidate
#print axioms CoarseWitness.local_sound
#print axioms indexed_local_coarse_certificate
end SparseMonotiles.CarrierHierarchy
