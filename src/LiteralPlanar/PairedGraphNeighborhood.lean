module

public import LiteralPlanar.GraphWindowBasis
public import LiteralPlanar.TwoSideOccupation

@[expose] public section


/-! A concrete graph-local version of two-sided occupation. It constructs the
open neighborhood from polynomial graph windows, rather than assuming that
the two bodies already cover a neighborhood. -/
namespace LiteralPlanar.Quintic
noncomputable section
open Set

theorem paired_graph_frontiers_cover_neighborhood (ε t : ℝ)
    (S T V : Set (ℝ × ℝ)) (hS : IsClosed S) (hT : IsClosed T)
    (hregS : S ⊆ closure (interior S)) (hregT : T ⊆ closure (interior T))
    (hpack : Disjoint (interior S) (interior T))
    (hV : IsOpen V) (hxV : (t,height ε t) ∈ V)
    (hxS : (t,height ε t) ∈ S) (hxT : (t,height ε t) ∈ T)
    (hfrontS : frontier S ∩ V = wholeGraph ε ∩ V)
    (hfrontT : frontier T ∩ V = wholeGraph ε ∩ V) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (t,height ε t) ∈ U ∧ U ⊆ S ∪ T := by
  obtain ⟨a,b,r,hat,htb,hr,hab,hxU,hUV⟩ := exists_graphWindow_subset ε t (t-1) (t+1)
    (by linarith) (by linarith) V hV hxV
  let U := graphWindow ε a b r
  let K := wholeGraph ε ∩ U
  have hlocal (A : Set (ℝ × ℝ)) (hA : frontier A ∩ V = wholeGraph ε ∩ V) :
      frontier A ∩ U = K := by
    ext x
    constructor
    · rintro ⟨hx,hxu⟩
      have hh : x ∈ frontier A ∩ V := ⟨hx,hUV hxu⟩
      rw [hA] at hh
      exact ⟨hh.1,hxu⟩
    · rintro ⟨hx,hxu⟩
      have hh : x ∈ wholeGraph ε ∩ V := ⟨hx,hUV hxu⟩
      rw [←hA] at hh
      exact ⟨hh.1,hxu⟩
  have hsides : U \ K = graphLower ε a b r ∪ graphUpper ε a b r := by
    have he : U \ K = U \ wholeGraph ε := by
      ext x
      constructor
      · rintro ⟨hu,hn⟩
        exact ⟨hu,fun hg => hn ⟨hg,hu⟩⟩
      · rintro ⟨hu,hn⟩
        exact ⟨hu,fun hh => hn hh.1⟩
    rw [he]
    exact graphWindow_sides ε a b r
  refine ⟨U,graphWindow_open ε a b r,hxU,?_⟩
  exact paired_bodies_cover_two_sided_neighborhood S T U K
    (graphLower ε a b r) (graphUpper ε a b r) (t,height ε t)
    hS hT hregS hregT (graphWindow_open ε a b r) hxS hxT hxU
    (hlocal S hfrontS) (hlocal T hfrontT) hsides
    (graphLower_connected ε a b r (lt_trans hat htb) hr)
    (graphUpper_connected ε a b r (lt_trans hat htb) hr) hpack

end
end LiteralPlanar.Quintic
