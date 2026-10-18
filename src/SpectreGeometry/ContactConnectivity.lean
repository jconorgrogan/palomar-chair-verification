module

public import SpectreGeometry.CompactTilingIncidence
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Logic.Relation

@[expose] public section


/-! Connectivity of actual closed-tile incidence in a preconnected space.
Contacts here may be single points. No whole-edge adjacency or orientation
registration is assumed or inferred. -/
namespace SpectreGeometry.CompactTilingIncidence
noncomputable section
open Set

def Contact {X ι : Type*} (F : ι → Set X) (i j : ι) : Prop := (F i ∩ F j).Nonempty

/-- A locally finite cover of a connected space by nonempty closed sets has
connected contact graph. The tiles themselves need not be connected. -/
theorem contact_connected {X ι : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (F : ι → Set X) (hlocal : LocallyFinite F) (hclosed : ∀ i, IsClosed (F i))
    (hnonempty : ∀ i, (F i).Nonempty) (hcover : ∀ x, ∃ i, x ∈ F i) (i j : ι) :
    Relation.ReflTransGen (Contact F) i j := by
  classical
  let P : ι → Prop := fun k => Relation.ReflTransGen (Contact F) i k
  let A : Set X := ⋃ k : {k // P k}, F k
  let B : Set X := ⋃ k : {k // ¬P k}, F k
  have hA : IsClosed A :=
    (hlocal.comp_injective Subtype.val_injective).isClosed_iUnion (fun k => hclosed k)
  have hB : IsClosed B :=
    (hlocal.comp_injective Subtype.val_injective).isClosed_iUnion (fun k => hclosed k)
  have hcoverAB : (Set.univ : Set X) ⊆ A ∪ B := by
    intro x hx
    obtain ⟨k,hk⟩ := hcover x
    by_cases hp : P k
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨k,hp⟩,hk⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k,hp⟩,hk⟩)
  have hAn : ((Set.univ : Set X) ∩ A).Nonempty := by
    obtain ⟨x,hx⟩ := hnonempty i
    exact ⟨x,Set.mem_univ x,Set.mem_iUnion.mpr ⟨⟨i,Relation.ReflTransGen.refl⟩,hx⟩⟩
  by_contra hnot
  have hBn : ((Set.univ : Set X) ∩ B).Nonempty := by
    obtain ⟨x,hx⟩ := hnonempty j
    exact ⟨x,Set.mem_univ x,Set.mem_iUnion.mpr ⟨⟨j,hnot⟩,hx⟩⟩
  obtain ⟨x,hx,hxa,hxb⟩ := isPreconnected_closed_iff.mp
    (isPreconnected_univ : IsPreconnected (Set.univ : Set X)) A B hA hB hcoverAB hAn hBn
  obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hxa
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hxb
  exact b.property (Relation.ReflTransGen.tail a.property ⟨x,ha,hb⟩)

/-- Any property propagated by every actual contact propagates through the
entire tiling; the local propagation theorem remains an explicit input. -/
theorem propagate_contact_property {X ι : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (F : ι → Set X) (hlocal : LocallyFinite F) (hclosed : ∀ i, IsClosed (F i))
    (hnonempty : ∀ i, (F i).Nonempty) (hcover : ∀ x, ∃ i, x ∈ F i)
    (P : ι → Prop) (hstep : ∀ i j, Contact F i j → P i → P j)
    (i : ι) (hi : P i) : ∀ j, P j := by
  intro j
  have h := contact_connected F hlocal hclosed hnonempty hcover i j
  induction h with
  | refl => exact hi
  | @tail b c hab hbc ih => exact hstep b c hbc ih

/-- Arbitrary isometric tilings by the concrete body have connected contact
graph, since local finiteness follows from their actual interior packing. -/
theorem polygon_tiling_contact_connected {ι : Type*}
    (f : ι → CompactPacking.Space 2 ≃ᵢ CompactPacking.Space 2)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (i j : ι) :
    Relation.ReflTransGen (Contact (fun k => f k '' euclideanBody)) i j := by
  have hbody : euclideanBody.Nonempty := euclideanBody_interior_nonempty.mono interior_subset
  exact contact_connected _ (CompactPacking.polygon_packing_locallyFinite f hdisjoint)
    (fun k => (euclideanBody_compact.image (f k).continuous).isClosed)
    (fun k => hbody.image (f k)) hcover i j

end
end SpectreGeometry.CompactTilingIncidence
