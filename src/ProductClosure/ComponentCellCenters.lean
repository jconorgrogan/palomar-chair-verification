module

public import ProductClosure.MatchedLatticeCells
public import ProductClosure.IntegralPoseGroup

@[expose] public section

namespace ProductClosure.NativeCompiler
open Set
noncomputable section
variable {m : ℕ} {S : Finset (LatticeIndex m)}
variable [Nonempty (Polycube.Cell S)]

/-- A component owns a lattice cell when its literal native occupied-cell
center maps to that lattice center in root coordinates. Registration will
turn this into equality of the entire closed unit cells. -/
def PhysicalTiling.ComponentCell {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (z : LatticeIndex m) : Prop :=
  ∃ i, T.KeyReachable root i ∧ ∃ c : Polycube.Cell S,
    relativePlacement (f root) (f i) (cellCenter c) = latticeCenter z

theorem PhysicalTiling.componentCell_nonempty
    {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) : ∃ z, T.ComponentCell root z := by
  let c : Polycube.Cell S := Classical.choice inferInstance
  refine ⟨cellIndex c, root, T.keyReachable_refl root, c, ?_⟩
  simp [relativePlacement, latticeCenter_cellIndex]

/-- Every exposed native facet of a reachable tile supplies its actual
outside-cell center from another reachable tile. -/
theorem PhysicalTiling.exists_reachable_outside_center
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {root i : ι} (hi : T.KeyReachable root i) (F : Facet S) :
    ∃ j, T.KeyReachable root j ∧ ∃ c : Polycube.Cell S,
      relativePlacement (f root) (f j) (cellCenter c) =
        relativePlacement (f root) (f i) (latticeCenter (facetOutsideIndex F)) := by
  let u : Site S := (F, Equiv.refl _, fun _ => true)
  obtain ⟨iv, hiv, _⟩ := T.unique_framed_key_companion hm i u
  have hreach : T.KeyReachable root iv.1 :=
    hi.tail ⟨Ne.symm hiv.1, u, iv.2, hiv.2.1⟩
  refine ⟨iv.1, hreach, facetInsideCell iv.2.1, ?_⟩
  have hc := matched_companion_cellCenter u iv.2 (f i) (f iv.1)
    hiv.2.2.1 hiv.2.2.2.1 hiv.2.2.2.2.1
  have hh := congrArg (f root).symm hc
  exact hh

end
end ProductClosure.NativeCompiler
