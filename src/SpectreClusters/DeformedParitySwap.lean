module

public import SpectreClusters.DeformedLiteralBinding
public import SpectreClusters.SwappedFieldCorrespondence

@[expose] public section


/-! The exact finite parity law for re-rooting at an old-frame hat.
No assertion of physical contact correspondence is included. -/
namespace SpectreClusters.DeformedLiteralBinding

set_option maxRecDepth 100000 in
theorem literalKind_add_odd_flip : ∀ a b : Fin 12,
    literalKind a = HTKind.hat →
    literalKind b = flipHTKind (literalKind (SpectreGeometry.directionAdd a b)) := by decide

set_option maxRecDepth 100000 in
theorem literalKind_add_even : ∀ a b : Fin 12,
    literalKind a = HTKind.turtle →
    literalKind (SpectreGeometry.directionAdd a b) = literalKind b := by decide

#print axioms literalKind_add_odd_flip
#print axioms literalKind_add_even

end SpectreClusters.DeformedLiteralBinding
