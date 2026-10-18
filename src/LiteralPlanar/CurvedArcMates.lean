module

public import LiteralPlanar.CurvedBoundary
public import LiteralPlanar.WholeArcRegistration
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section


/-! Every literal boundary arc in an arbitrary physical curved-body tiling
has a whole-arc partner. The tiling index is unrestricted; compactness and
packing derive the finite neighbor set used in the argument. -/
namespace LiteralPlanar.Candidate
noncomputable section
open SpectreGeometry

theorem euclideanArc_compact (e : Fin 14) : IsCompact (euclideanArc e) := by
  have hc : Continuous (edgeCurve e) := by unfold edgeCurve Quintic.height; fun_prop
  exact (isCompact_Icc.image hc).image euclideanCoordinates.continuous

theorem euclideanArc_set_infinite (e : Fin 14) : (euclideanArc e).Infinite := by
  rw [euclideanArc_eq_chart_image]
  have hi : (Quintic.standardArc Quintic.amplitude).Infinite :=
    (Set.Icc_infinite (by norm_num : (-1/2 : ℝ)<1/2)).image
      (Quintic.standardArc_parameter_injective Quintic.amplitude).injOn
  exact hi.image (edgeChart e).injective.injOn

end
end LiteralPlanar.Candidate

namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry SpectreGeometry.CompactTilingIncidence Candidate FanBounds Set
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)
include p T root

theorem curved_physical_whole_arc_mate {J : Type*}
    (q : J → EPlane ≃ᵢ EPlane)
    (hcover : ∀ x, ∃ j, x ∈ q j '' curvedBody)
    (hpack : Pairwise fun i j => Disjoint (interior (q i '' curvedBody))
      (interior (q j '' curvedBody))) (i : J) (e : Fin 14) :
    ∃ j : J, j ≠ i ∧ ∃ d : Fin 14, q i '' euclideanArc e = q j '' euclideanArc d := by
  classical
  let A := q i '' euclideanArc e
  let F := fun j => q j '' curvedBody
  have hclosed (j : J) : IsClosed (F j) :=
    (curvedBody_compact.image (q j).continuous).isClosed
  have hregular (j : J) : F j ⊆ closure (interior (F j)) := by
    change q j '' curvedBody ⊆ closure (interior (q j '' curvedBody))
    simp only [←IsometryEquiv.coe_toHomeomorph (q j)]
    rw [←(q j).toHomeomorph.image_interior,←(q j).toHomeomorph.image_closure,
      curvedBody_closure_interior p T root]
  have hlocal : LocallyFinite F := CompactPacking.locallyFinite curvedBody curvedBody_compact
    (curvedBody_interior_nonempty p T root) q hpack
  have hfront (j : J) : frontier (F j) = ⋃ d : Fin 14, q j '' euclideanArc d := by
    change frontier (q j '' curvedBody) = _
    simp only [←IsometryEquiv.coe_toHomeomorph (q j)]
    rw [←(q j).toHomeomorph.image_frontier,curvedBody_frontier p T root]
    simp only [curvedBoundary,candidateBoundary,Set.image_iUnion,euclideanArc,Set.image_image]
  have hA : IsCompact A := (euclideanArc_compact e).image (q i).continuous
  have hneighbors : {j : J | (A ∩ F j).Nonempty}.Finite := by
    have hh := hlocal.finite_nonempty_inter_compact hA
    simpa only [Set.inter_comm] using hh
  let N := {j : J // j ≠ i ∧ (A ∩ F j).Nonempty}
  have hN : {j : J | j ≠ i ∧ (A ∩ F j).Nonempty}.Finite :=
    hneighbors.subset (fun _ h => h.2)
  letI : Fintype N := hN.fintype
  have hsub : A ⊆ ⋃ j : N, ⋃ d : Fin 14, A ∩ (q j.val '' euclideanArc d) := by
    intro x hx
    have hxi : x ∈ frontier (F i) := by
      rw [hfront]
      exact mem_iUnion.mpr ⟨e,hx⟩
    obtain ⟨j,hji,hjx⟩ := frontier_has_boundary_neighbor F hlocal hclosed hregular hpack hcover i hxi
    have hxj : x ∈ F j := (hclosed j).closure_subset hjx.1
    obtain ⟨d,hd⟩ := mem_iUnion.mp ((hfront j) ▸ hjx)
    exact mem_iUnion.mpr ⟨⟨j,hji,⟨x,hx,hxj⟩⟩,mem_iUnion.mpr ⟨d,hx,hd⟩⟩
  have hinfinite : A.Infinite := (euclideanArc_set_infinite e).image (q i).injective.injOn
  have hmate : ∃ j : N, ∃ d : Fin 14, (A ∩ q j.val '' euclideanArc d).Infinite := by
    by_contra hn
    have hfinite : ∀ j : N, ∀ d : Fin 14, (A ∩ q j.val '' euclideanArc d).Finite := by
      intro j d
      exact not_not.mp (fun hh => hn ⟨j,d,hh⟩)
    exact hinfinite ((Set.finite_iUnion (fun j => Set.finite_iUnion (hfinite j))).subset hsub)
  obtain ⟨j,d,hd⟩ := hmate
  exact ⟨j.val,j.property.1,d,infinite_placed_edgeArcs_whole (q i) (q j.val) e d hd⟩

end
end LiteralPlanar.Forward
