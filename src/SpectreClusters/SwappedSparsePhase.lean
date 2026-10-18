module

public import SpectreClusters.SwappedFieldCorrespondence
public import SpectreClusters.StageAPhasePropagation

@[expose] public section


/-! Finite phase reversal once a genuine alternate-field correspondence is
supplied. Constructing it from physical root change is a separate obligation. -/
namespace SpectreClusters.StageA

theorem sparseHats_to_sparseTurtles {f g : Cell → HTPlacement}
    (E : SwappedFieldCorrespondence f g) (h : SparseHats f) : SparseTurtles g := by
  intro q hq
  let q' : OwnedTile g := ⟨q,hq⟩
  let p := E.inverse q'
  have hp : SparseTurtlesAt g (E.occurrences p).val :=
    (E.sparseTurtlesAt_iff_not p).mpr (h p.val p.property)
  simpa only [p,E.occurrences_inverse] using hp

/-- Precisely the two-field branch resolution needed by the physical bridge. -/
theorem one_of_swapped_fields_sparse (hcaptures : FinalCaptures)
    (f g : Cell → HTPlacement) (hf : ValidGridField f)
    (E : SwappedFieldCorrespondence f g) : SparseTurtles f ∨ SparseTurtles g := by
  rcases global_sparse_dichotomy hcaptures f hf with h | h
  · exact Or.inl h
  · exact Or.inr (sparseHats_to_sparseTurtles E h)

end SpectreClusters.StageA
