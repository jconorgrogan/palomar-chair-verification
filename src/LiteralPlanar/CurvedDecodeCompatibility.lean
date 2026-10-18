module

public import LiteralPlanar.CurvedGraphNeighborhood
public import LiteralPlanar.CurvedInverseMaps

@[expose] public section


/-! Universal contact compatibility of the explicit inverse tile maps.
Arbitrary contacts are handled by strict-arc registration or fixed vertices;
no contact decomposition is supplied as an assumption. -/
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry SpectreGeometry.CompactTilingIncidence Candidate FanBounds Set
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)

theorem curved_inverse_contact_compatible {J : Type*} (q : J → EPlane ≃ᵢ EPlane)
    (hcover : ∀ x, ∃ j, x ∈ q j '' curvedBody)
    (hpack : Pairwise fun i j => Disjoint (interior (q i '' curvedBody))
      (interior (q j '' curvedBody))) (i j : J) (x : EPlane)
    (hxi : x ∈ q i '' curvedBody) (hxj : x ∈ q j '' curvedBody) :
    placedInverse p T root (q i) x = placedInverse p T root (q j) x := by
  classical
  by_cases hij : i=j
  · subst j
    rfl
  have closed (k : J) : IsClosed (q k '' curvedBody) :=
    (curvedBody_compact.image (q k).continuous).isClosed
  have reg (k : J) : q k '' curvedBody ⊆ closure (interior (q k '' curvedBody)) := by
    simp only [←IsometryEquiv.coe_toHomeomorph (q k)]
    rw [←(q k).toHomeomorph.image_interior,←(q k).toHomeomorph.image_closure,
      curvedBody_closure_interior p T root]
  have nonvertex_agrees (a b : J) (hab : a ≠ b)
      (hxa : x ∈ q a '' curvedBody) (hxb : x ∈ q b '' curvedBody)
      (hnv : ∀ e : Fin 14, x ≠ q a (euclideanVertex e)) :
      placedInverse p T root (q a) x = placedInverse p T root (q b) x := by
    have hfront := common_point_frontiers (fun k => q k '' curvedBody)
      closed reg hpack hab hxa hxb
    obtain ⟨e,t,ht,ht',hpoint⟩ := curved_nonvertex_frontier_arc p T root (q a) x hfront.1 hnv
    obtain ⟨d,hwhole⟩ := curved_strict_contact_whole_arc p T root q hcover hpack a b hab.symm
      e t ht ht' (hpoint ▸ hxb)
    have hinf : (q a '' euclideanArc e ∩ q b '' euclideanArc d).Infinite := by
      rw [←hwhole,Set.inter_self]
      exact (euclideanArc_set_infinite e).image (q a).injective.injOn
    apply placedInverse_agrees_on_matched_arcs p T root (q a) (q b) e d hinf x
    rw [hpoint]
    exact ⟨_,⟨_,⟨t,⟨ht.le,ht'.le⟩,rfl⟩,rfl⟩,rfl⟩
  by_cases hvi : ∃ e : Fin 14, x = q i (euclideanVertex e)
  · by_cases hvj : ∃ d : Fin 14, x = q j (euclideanVertex d)
    · obtain ⟨e,he⟩ := hvi
      obtain ⟨d,hd⟩ := hvj
      calc
        _ = x := by rw [he,placedInverse_vertex]
        _ = _ := by rw [hd,placedInverse_vertex]
    · exact (nonvertex_agrees j i (Ne.symm hij) hxj hxi (by simpa only [not_exists] using hvj)).symm
  · exact nonvertex_agrees i j hij hxi hxj (by simpa only [not_exists] using hvi)

end
end LiteralPlanar.Forward
