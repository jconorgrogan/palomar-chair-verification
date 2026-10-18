module

public import LiteralPlanar.CurvedIncidence
public import LiteralPlanar.ArcParameterRegistration
public import LiteralPlanar.GraphImageNeighborhood

@[expose] public section


/-! Actual paired-arc graph neighborhoods for arbitrary physical placements.
Every local frontier equality is derived from the literal polynomial arcs. -/
namespace LiteralPlanar.Candidate
noncomputable section
open SpectreGeometry Set

def placedArcChart (f : EPlane ≃ᵢ EPlane) (e : Fin 14) : (ℝ × ℝ) ≃ₜ EPlane :=
  euclideanCoordinates.trans ((edgeChart e).toHomeomorph.trans f.toHomeomorph)

theorem placedArcChart_graph (f : EPlane ≃ᵢ EPlane) (e : Fin 14) (t : ℝ) :
    placedArcChart f e (t,Quintic.height Quintic.amplitude t) =
      f (euclideanCoordinates (edgeCurve e t)) := by
  simp only [placedArcChart,Homeomorph.trans_apply,IsometryEquiv.coe_toHomeomorph,
    edgeChart_graph]

def strictArcStrip : Set (ℝ × ℝ) := Ioo (-1/2 : ℝ) (1/2) ×ˢ univ

theorem placed_arc_graph_iff (f : EPlane ≃ᵢ EPlane) (e : Fin 14) (x : EPlane)
    (hx : x ∈ placedArcChart f e '' strictArcStrip) :
    x ∈ f '' euclideanArc e ↔ x ∈ placedArcChart f e '' Quintic.wholeGraph Quintic.amplitude := by
  let H := placedArcChart f e
  have he : f '' euclideanArc e = H '' ((fun t => (t,Quintic.height Quintic.amplitude t)) ''
      Icc (-1/2 : ℝ) (1/2)) := by
    simp only [euclideanArc,Set.image_image]
    apply Set.image_congr
    intro t ht
    exact (placedArcChart_graph f e t).symm
  obtain ⟨y,hy,rfl⟩ := hx
  rw [he,H.injective.mem_set_image,H.injective.mem_set_image]
  constructor
  · rintro ⟨t,ht,rfl⟩
    rfl
  · intro hgraph
    exact ⟨y.1,⟨hy.1.1.le,hy.1.2.le⟩,Prod.ext rfl hgraph.symm⟩

end
end LiteralPlanar.Candidate

namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry Candidate FanBounds Set
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)
include p T root

theorem placed_strict_arc_local_frontier (f : EPlane ≃ᵢ EPlane) (e : Fin 14) (t : ℝ)
    (ht : -1/2 < t) (ht' : t < 1/2) :
    ∃ U : Set EPlane, IsOpen U ∧ f (euclideanCoordinates (edgeCurve e t)) ∈ U ∧
      frontier (f '' curvedBody) ∩ U = (f '' euclideanArc e) ∩ U := by
  obtain ⟨U,hU,hxU,he⟩ := strict_curve_local_frontier p T root e t ht ht'
  refine ⟨f '' U,f.toHomeomorph.isOpenMap _ hU,⟨_,hxU,rfl⟩,?_⟩
  have hf : f '' frontier curvedBody = frontier (f '' curvedBody) := by
    simpa only [IsometryEquiv.coe_toHomeomorph] using f.toHomeomorph.image_frontier curvedBody
  rw [←hf,←Set.image_inter f.injective,he,
    Set.image_inter f.injective]

theorem matched_strict_arcs_cover_neighborhood (f g : EPlane ≃ᵢ EPlane)
    (e d : Fin 14) (t s : ℝ) (ht : -1/2 < t) (ht' : t < 1/2)
    (hs : -1/2 < s) (hs' : s < 1/2)
    (hpoint : f (euclideanCoordinates (edgeCurve e t)) =
      g (euclideanCoordinates (edgeCurve d s)))
    (hwhole : f '' euclideanArc e = g '' euclideanArc d)
    (hpack : Disjoint (interior (f '' curvedBody)) (interior (g '' curvedBody))) :
    ∃ U : Set EPlane, IsOpen U ∧ f (euclideanCoordinates (edgeCurve e t)) ∈ U ∧
      U ⊆ f '' curvedBody ∪ g '' curvedBody := by
  obtain ⟨U,hU,hxU,hfrontU⟩ := placed_strict_arc_local_frontier p T root f e t ht ht'
  obtain ⟨V,hV,hxV,hfrontV⟩ := placed_strict_arc_local_frontier p T root g d s hs hs'
  let H := placedArcChart f e
  let W := (U ∩ V) ∩ H '' strictArcStrip
  have hW : IsOpen W := (hU.inter hV).inter
    (H.isOpenMap _ (isOpen_Ioo.prod isOpen_univ))
  have hxW : H (t,Quintic.height Quintic.amplitude t) ∈ W := by
    refine ⟨⟨?_,?_⟩,⟨_,⟨⟨ht,ht'⟩,mem_univ _⟩,rfl⟩⟩
    · simpa only [H,placedArcChart_graph] using hxU
    · simpa only [H,placedArcChart_graph,hpoint] using hxV
  have graphF : frontier (f '' curvedBody) ∩ W = H '' Quintic.wholeGraph Quintic.amplitude ∩ W := by
    ext x
    constructor
    · rintro ⟨hx,hw⟩
      have ha : x ∈ f '' euclideanArc e := (hfrontU ▸ (show x ∈ frontier (f '' curvedBody) ∩ U from ⟨hx,hw.1.1⟩)).1
      exact ⟨(placed_arc_graph_iff f e x hw.2).mp ha,hw⟩
    · rintro ⟨hx,hw⟩
      have ha := (placed_arc_graph_iff f e x hw.2).mpr hx
      exact ⟨(hfrontU.symm ▸ (show x ∈ (f '' euclideanArc e) ∩ U from ⟨ha,hw.1.1⟩)).1,hw⟩
  have graphG : frontier (g '' curvedBody) ∩ W = H '' Quintic.wholeGraph Quintic.amplitude ∩ W := by
    ext x
    constructor
    · rintro ⟨hx,hw⟩
      have ha : x ∈ g '' euclideanArc d := (hfrontV ▸ (show x ∈ frontier (g '' curvedBody) ∩ V from ⟨hx,hw.1.2⟩)).1
      rw [←hwhole] at ha
      exact ⟨(placed_arc_graph_iff f e x hw.2).mp ha,hw⟩
    · rintro ⟨hx,hw⟩
      have ha := (placed_arc_graph_iff f e x hw.2).mpr hx
      rw [hwhole] at ha
      exact ⟨(hfrontV.symm ▸ (show x ∈ (g '' euclideanArc d) ∩ V from ⟨ha,hw.1.2⟩)).1,hw⟩
  have closed (q : EPlane ≃ᵢ EPlane) : IsClosed (q '' curvedBody) :=
    (curvedBody_compact.image q.continuous).isClosed
  have reg (q : EPlane ≃ᵢ EPlane) : q '' curvedBody ⊆ closure (interior (q '' curvedBody)) := by
    simp only [←IsometryEquiv.coe_toHomeomorph q]
    rw [←q.toHomeomorph.image_interior,←q.toHomeomorph.image_closure,
      curvedBody_closure_interior p T root]
  have arcpoint : f (euclideanCoordinates (edgeCurve e t)) ∈ f '' euclideanArc e :=
    ⟨_,⟨_,⟨t,⟨ht.le,ht'.le⟩,rfl⟩,rfl⟩,rfl⟩
  have hxF : H (t,Quintic.height Quintic.amplitude t) ∈ f '' curvedBody := by
    simp only [H,placedArcChart_graph]
    exact (closed f).closure_subset (hfrontU.symm ▸ (show f (euclideanCoordinates (edgeCurve e t)) ∈ (f '' euclideanArc e) ∩ U from ⟨arcpoint,hxU⟩)).1.1
  have hxG : H (t,Quintic.height Quintic.amplitude t) ∈ g '' curvedBody := by
    rw [hwhole] at arcpoint
    simp only [H,placedArcChart_graph]
    exact (closed g).closure_subset
      (hfrontV.symm ▸ (show f (euclideanCoordinates (edgeCurve e t)) ∈ (g '' euclideanArc d) ∩ V from ⟨arcpoint,hpoint.symm ▸ hxV⟩)).1.1
  obtain ⟨Z,hZ,hxZ,hcover⟩ := Quintic.paired_graph_image_frontiers_cover_neighborhood
    H Quintic.amplitude t (f '' curvedBody) (g '' curvedBody) W
    (closed f) (closed g) (reg f) (reg g) hpack hW hxW hxF hxG graphF graphG
  exact ⟨Z,hZ,by simpa only [H,placedArcChart_graph] using hxZ,hcover⟩

/-- Every contact at a strict arc point belongs to that arc's whole partner.
This is derived for an arbitrary physical tiling; no edge-to-edge assumption is used. -/
theorem curved_strict_contact_whole_arc {J : Type*} (q : J → EPlane ≃ᵢ EPlane)
    (hcover : ∀ x, ∃ j, x ∈ q j '' curvedBody)
    (hpack : Pairwise fun i j => Disjoint (interior (q i '' curvedBody))
      (interior (q j '' curvedBody))) (i k : J) (hki : k ≠ i)
    (e : Fin 14) (t : ℝ) (ht : -1/2 < t) (ht' : t < 1/2)
    (hxk : q i (euclideanCoordinates (edgeCurve e t)) ∈ q k '' curvedBody) :
    ∃ d : Fin 14, q i '' euclideanArc e = q k '' euclideanArc d := by
  obtain ⟨j,hji,d,hwhole⟩ := curved_physical_whole_arc_mate p T root q hcover hpack i e
  have hi : (q i '' euclideanArc e ∩ q j '' euclideanArc d).Infinite := by
    rw [←hwhole,Set.inter_self]
    exact (euclideanArc_set_infinite e).image (q i).injective.injOn
  have hparam := infinite_placed_edgeArcs_parameters (q i) (q j) e d hi
  have hneighborhood : ∃ U : Set EPlane, IsOpen U ∧ q i (euclideanCoordinates (edgeCurve e t)) ∈ U ∧
      U ⊆ q i '' curvedBody ∪ q j '' curvedBody := by
    rcases hparam with hp | hp
    · exact matched_strict_arcs_cover_neighborhood p T root (q i) (q j) e d t t
        ht ht' ht ht' (hp t) hwhole (hpack hji.symm)
    · exact matched_strict_arcs_cover_neighborhood p T root (q i) (q j) e d t (-t)
        ht ht' (by linarith) (by linarith) (hp t) hwhole (hpack hji.symm)
  by_cases hkj : k=j
  · exact ⟨d,hkj.symm ▸ hwhole⟩
  · obtain ⟨U,hU,hxU,hUC⟩ := hneighborhood
    have reg (l : J) : q l '' curvedBody ⊆ closure (interior (q l '' curvedBody)) := by
      simp only [←IsometryEquiv.coe_toHomeomorph (q l)]
      rw [←(q l).toHomeomorph.image_interior,←(q l).toHomeomorph.image_closure,
        curvedBody_closure_interior p T root]
    exact (no_third_contact_in_paired_neighborhood (q i '' curvedBody) (q j '' curvedBody)
      (q k '' curvedBody) U _ (reg i) (reg j) (reg k) hU hxU hUC
      (hpack hki.symm) (hpack (Ne.symm hkj)) hxk).elim

end
end LiteralPlanar.Forward
