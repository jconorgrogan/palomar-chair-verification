module

public import LiteralPlanar.CurvedBoundary

@[expose] public section


/-! Small checked proof-application interface for the existing closed P seed.
It does not import the seed's large closure. A closed final application must be
kernel-checked separately against the exact original theorem constant. -/
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry FanBounds

abbrev OriginalSeedStatement : Prop :=
  ∃ (I : Type) (p : I → EPlane ≃ᵢ EPlane),
    (∀ i, DirectPlacement (p i)) ∧
    (∀ x : EPlane, ∃ i, x ∈ p i '' euclideanBody) ∧
    Pairwise (fun i j => Disjoint (interior (p i '' euclideanBody))
      (interior (p j '' euclideanBody))) ∧
    LocallyFinite (fun i => p i '' euclideanBody)

/-- All stated target geometry and physical coverage/packing are derived from
the exact original-P existence statement and the explicit polynomial maps. -/
theorem curved_geometry_and_tiling_of_original_seed (hseed :
  ∃ (I : Type) (p : I → EPlane ≃ᵢ EPlane),
    (∀ i, DirectPlacement (p i)) ∧
    (∀ x : EPlane, ∃ i, x ∈ p i '' euclideanBody) ∧
    Pairwise (fun i j => Disjoint (interior (p i '' euclideanBody))
      (interior (p j '' euclideanBody))) ∧
    LocallyFinite (fun i => p i '' euclideanBody)) :
    IsCompact curvedBody ∧ (interior curvedBody).Nonempty ∧
      closure (interior curvedBody) = curvedBody ∧
      frontier curvedBody = curvedBoundary ∧
      ∃ (I : Type) (p : I → EPlane ≃ᵢ EPlane),
        (∀ i, DirectPlacement (p i)) ∧
        (∀ x : EPlane, ∃ i, x ∈ p i '' curvedBody) ∧
        Pairwise (fun i j => Disjoint (interior (p i '' curvedBody))
          (interior (p j '' curvedBody))) ∧
        LocallyFinite (fun i => p i '' curvedBody) := by
  obtain ⟨I,p,hd,hcover,hpacking,hlocal⟩ := hseed
  let T : SourceTiling p := ⟨hd,hcover,hpacking⟩
  obtain ⟨i,hi⟩ := hcover 0
  have hn := curvedBody_interior_nonempty p T i
  obtain ⟨hc,hp⟩ := source_tiling_to_curved_tiling p T
  exact ⟨LiteralPlanar.curvedBody_compact,hn,curvedBody_closure_interior p T i,
    curvedBody_frontier p T i,I,p,hd,hc,hp,
    CompactPacking.locallyFinite curvedBody LiteralPlanar.curvedBody_compact hn p hp⟩

end
end LiteralPlanar.Forward
