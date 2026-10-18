module

public import SpectreClusters.GridNeighborInvariant

@[expose] public section


/-! A precise finite interface for the alternate parity deformation.
This does not construct a second field or assume it has valid coverage. -/
namespace SpectreClusters

def flipHTKind : HTKind → HTKind
  | .hat => .turtle
  | .turtle => .hat

theorem flipHTKind_injective {a b : HTKind} (h : flipHTKind a = flipHTKind b) : a = b := by
  cases a <;> cases b <;> simp_all [flipHTKind]

abbrev OwnedTile (f : Cell → HTPlacement) := { p : HTPlacement // RootOwned f p }

/-- A source-correct physical instantiation must match the same original tile.
The finite interface itself records only the exact occurrence/contact laws. -/
structure SwappedFieldCorrespondence (f g : Cell → HTPlacement) where
  occurrences : OwnedTile f → OwnedTile g
  inverse : OwnedTile g → OwnedTile f
  inverse_occurrences : ∀ p, inverse (occurrences p) = p
  occurrences_inverse : ∀ q, occurrences (inverse q) = q
  kind_flip : ∀ p, (occurrences p).val.kind = flipHTKind p.val.kind
  neighbor_iff : ∀ p q,
    StageA.FieldNeighbor g (occurrences p).val (occurrences q).val ↔
      StageA.FieldNeighbor f p.val q.val

namespace SwappedFieldCorrespondence

theorem allOpposite_iff {f g : Cell → HTPlacement}
    (E : SwappedFieldCorrespondence f g) (p : OwnedTile f) :
    AllOppositeNeighbors g (E.occurrences p).val ↔ AllOppositeNeighbors f p.val := by
  constructor
  · intro h q hq he
    let q' : OwnedTile f := ⟨q,hq.1⟩
    have hn := h (E.occurrences q').val ((E.neighbor_iff p q').mpr hq)
    apply hn
    rw [E.kind_flip q', E.kind_flip p]
    exact congrArg flipHTKind he
  · intro h q hq he
    let q' : OwnedTile g := ⟨q,hq.1⟩
    let r := E.inverse q'
    have her : E.occurrences r = q' := E.occurrences_inverse q'
    have hn : StageA.FieldNeighbor f p.val r.val := by
      apply (E.neighbor_iff p r).mp
      simpa only [her] using hq
    apply h r.val hn
    apply flipHTKind_injective
    rw [←E.kind_flip r, ←E.kind_flip p]
    simpa only [her] using he

/-- A genuine kind-swapping contact equivalence reverses the global sparse phase. -/
theorem sparseTurtlesAt_iff_not {f g : Cell → HTPlacement}
    (E : SwappedFieldCorrespondence f g) (p : OwnedTile f) :
    SparseTurtlesAt g (E.occurrences p).val ↔ ¬SparseTurtlesAt f p.val := by
  classical
  unfold SparseTurtlesAt
  rw [E.allOpposite_iff p, E.kind_flip p]
  cases hk : p.val.kind <;> simp [flipHTKind]

end SwappedFieldCorrespondence
end SpectreClusters
