module

public import LiteralPlanar.CountableContactChirality
public import SpectreGeometry.CompactTilingIncidence
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section


/-! The closed-color argument applied to a genuine locally finite tiling.
There is no edge-graph connectivity premise. The remaining geometric input is
countability of contact between tiles of opposite colors. -/
namespace LiteralPlanar
noncomputable section
open Set SpectreGeometry.CompactTilingIncidence

theorem tiling_color_constant {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SigmaCompactSpace E] (hdim : 1 < Module.rank ℝ E)
    (F : I → Set E) (c : I → Prop)
    (hlocal : LocallyFinite F) (hclosed : ∀ i, IsClosed (F i))
    (hregular : ∀ i, F i ⊆ closure (interior (F i)))
    (hinterior : ∀ i, (interior (F i)).Nonempty)
    (hpack : Pairwise fun i j => Disjoint (interior (F i)) (interior (F j)))
    (hcover : ∀ x, ∃ i, x ∈ F i)
    (hcontact : ∀ i j, c i → ¬c j → (F i ∩ F j).Countable) :
    ∀ i j, c i ↔ c j := by
  classical
  have hcount : (univ : Set I).Countable :=
    hlocal.countable_univ (fun i => (hinterior i).mono interior_subset)
  letI : Countable I := Set.countable_univ_iff.mp hcount
  let A : Set E := ⋃ i : {i // c i}, F i
  let B : Set E := ⋃ i : {i // ¬c i}, F i
  have hA : IsClosed A := (hlocal.comp_injective Subtype.val_injective).isClosed_iUnion
    (fun i => hclosed i)
  have hB : IsClosed B := (hlocal.comp_injective Subtype.val_injective).isClosed_iUnion
    (fun i => hclosed i)
  have hAB : A ∪ B = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i,hi⟩ := hcover x
    by_cases hc : c i
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i,hc⟩,hi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨i,hc⟩,hi⟩)
  have hcontactAB : (A ∩ B).Countable := by
    have hh : (⋃ i : {i // c i}, ⋃ j : {j // ¬c j}, F i ∩ F j).Countable :=
      countable_iUnion (fun i => countable_iUnion (fun j => hcontact i j i.property j.property))
    apply hh.mono
    rintro x ⟨hxA,hxB⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxA
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxB
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,hi,hj⟩⟩
  have hnomixed (i j : I) (hi : c i) (hj : ¬c j) : False := by
    obtain ⟨x,hx⟩ := hinterior i
    obtain ⟨y,hy⟩ := hinterior j
    apply no_closed_color_separation hdim A B hA hB hAB hcontactAB
    · refine ⟨x,mem_iUnion.mpr ⟨⟨i,hi⟩,interior_subset hx⟩,?_⟩
      intro hxB
      obtain ⟨k,hk⟩ := mem_iUnion.mp hxB
      have hki : (k : I) ≠ i := by intro he; exact k.property (he ▸ hi)
      exact Set.disjoint_left.mp (tile_disjoint_other_interior F hregular hpack hki) hk hx
    · refine ⟨y,mem_iUnion.mpr ⟨⟨j,hj⟩,interior_subset hy⟩,?_⟩
      intro hyA
      obtain ⟨k,hk⟩ := mem_iUnion.mp hyA
      have hkj : (k : I) ≠ j := by intro he; exact hj (he ▸ k.property)
      exact Set.disjoint_left.mp (tile_disjoint_other_interior F hregular hpack hkj) hk hy
  intro i j
  constructor
  · intro hi
    by_contra hj
    exact hnomixed i j hi hj
  · intro hj
    by_contra hi
    exact hnomixed j i hj hi

end
end LiteralPlanar
