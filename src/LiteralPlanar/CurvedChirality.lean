module

public import LiteralPlanar.ArcOrientation
public import LiteralPlanar.CurvedBoundary
public import LiteralPlanar.TilingColorConstancy

@[expose] public section


/-! Actual unrestricted physical tilings of the literal polynomial body have
one common handedness. The common sign is allowed to be negative. -/
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry SpectreGeometry.CompactTilingIncidence Candidate FanBounds Set
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)
include p T root

theorem curved_frontier_arcs : frontier curvedBody = ⋃ e : Fin 14, euclideanArc e := by
  rw [curvedBody_frontier p T root]
  simp only [curvedBoundary,Candidate.candidateBoundary,Set.image_iUnion,euclideanArc]

theorem opposite_curved_body_contacts_finite {J : Type*}
    (q : J → EPlane ≃ᵢ EPlane)
    (hpack : Pairwise fun i j => Disjoint (interior (q i '' curvedBody))
      (interior (q j '' curvedBody))) (i j : J)
    (hopp : orientationDet (q i) ≠ orientationDet (q j)) :
    (q i '' curvedBody ∩ q j '' curvedBody).Finite := by
  have hclosed (k : J) : IsClosed (q k '' curvedBody) :=
    (curvedBody_compact.image (q k).continuous).isClosed
  have hregular (k : J) : q k '' curvedBody ⊆ closure (interior (q k '' curvedBody)) := by
    simp only [←IsometryEquiv.coe_toHomeomorph (q k)]
    rw [←(q k).toHomeomorph.image_interior,←(q k).toHomeomorph.image_closure,
      curvedBody_closure_interior p T root]
  have hij : i ≠ j := by intro he; exact hopp (congrArg (fun k => orientationDet (q k)) he)
  have hf (k : J) : frontier (q k '' curvedBody) = ⋃ e : Fin 14, q k '' euclideanArc e := by
    simp only [←IsometryEquiv.coe_toHomeomorph (q k)]
    rw [←(q k).toHomeomorph.image_frontier,curved_frontier_arcs p T root,Set.image_iUnion]
  have hfinite : (⋃ e : Fin 14, ⋃ d : Fin 14,
      q i '' euclideanArc e ∩ q j '' euclideanArc d).Finite :=
    Set.finite_iUnion (fun e => Set.finite_iUnion (fun d =>
      opposite_placed_edgeArcs_contact_finite (q i) (q j) hopp e d))
  apply hfinite.subset
  rintro x ⟨hi,hj⟩
  obtain ⟨hix,hjx⟩ := common_point_frontiers (fun k => q k '' curvedBody)
    hclosed hregular hpack hij hi hj
  rw [hf] at hix hjx
  obtain ⟨e,he⟩ := mem_iUnion.mp hix
  obtain ⟨d,hd⟩ := mem_iUnion.mp hjx
  exact mem_iUnion.mpr ⟨e,mem_iUnion.mpr ⟨d,he,hd⟩⟩

theorem curved_tiling_common_orientation {J : Type*}
    (q : J → EPlane ≃ᵢ EPlane)
    (hcover : ∀ x, ∃ j, x ∈ q j '' curvedBody)
    (hpack : Pairwise fun i j => Disjoint (interior (q i '' curvedBody))
      (interior (q j '' curvedBody))) :
    ∀ i j, orientationDet (q i) = orientationDet (q j) := by
  have hclosed (k : J) : IsClosed (q k '' curvedBody) :=
    (curvedBody_compact.image (q k).continuous).isClosed
  have hregular (k : J) : q k '' curvedBody ⊆ closure (interior (q k '' curvedBody)) := by
    simp only [←IsometryEquiv.coe_toHomeomorph (q k)]
    rw [←(q k).toHomeomorph.image_interior,←(q k).toHomeomorph.image_closure,
      curvedBody_closure_interior p T root]
  have hinterior (k : J) : (interior (q k '' curvedBody)).Nonempty := by
    simp only [←IsometryEquiv.coe_toHomeomorph (q k)]
    rw [←(q k).toHomeomorph.image_interior]
    exact (curvedBody_interior_nonempty p T root).image _
  have hlocal := CompactPacking.locallyFinite curvedBody curvedBody_compact
    (curvedBody_interior_nonempty p T root) q hpack
  have hdim : 1 < Module.rank ℝ EPlane := by
    rw [←Module.finrank_eq_rank]
    norm_num [EPlane,finrank_euclideanSpace_fin]
  have hc := tiling_color_constant hdim (fun j => q j '' curvedBody)
    (fun j => orientationDet (q j)=1) hlocal hclosed hregular hinterior hpack hcover
    (fun i j hi hj => (opposite_curved_body_contacts_finite p T root q hpack i j
      (fun he => hj (he ▸ hi))).countable)
  intro i j
  rcases orientationDet_sign (q i) with hi | hi
  · exact hi.trans ((hc i j).mp hi).symm
  · rcases orientationDet_sign (q j) with hj | hj
    · have hh := (hc i j).mpr hj
      linarith
    · exact hi.trans hj.symm

/-- Pick any actual tile as the ambient reference frame. This simultaneously
handles the all-positive and all-reflected possibilities. -/
theorem normalized_curved_placements_direct {J : Type*}
    (q : J → EPlane ≃ᵢ EPlane)
    (hcover : ∀ x, ∃ j, x ∈ q j '' curvedBody)
    (hpack : Pairwise fun i j => Disjoint (interior (q i '' curvedBody))
      (interior (q j '' curvedBody))) (base : J) :
    ∀ j, DirectPlacement ((q j).trans (q base).symm) := by
  intro j
  exact same_orientation_relative_direct (q j) (q base)
    (curved_tiling_common_orientation p T root q hcover hpack j base)

end
end LiteralPlanar.Forward
