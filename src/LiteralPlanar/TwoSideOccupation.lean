module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.ClusterPt

@[expose] public section


/-! The local topological two-sided occupation lemma needed to exclude third
tile contacts after whole-arc matching. The geometric application must exhibit
its actual two connected graph sides and its local frontier equalities. -/
namespace LiteralPlanar
noncomputable section
open Set
variable {X : Type*} [TopologicalSpace X]

theorem preconnected_side_dichotomy (S Q : Set X) (hS : IsClosed S)
    (hQ : IsPreconnected Q) (havoid : ∀ x ∈ Q, x ∉ frontier S) :
    Q ⊆ interior S ∨ Q ⊆ Sᶜ := by
  apply hQ.subset_or_subset isOpen_interior hS.isOpen_compl
  · exact disjoint_left.mpr fun x hx hxc => hxc (interior_subset hx)
  · intro x hx
    by_cases hs : x ∈ S
    · left
      by_contra hi
      apply havoid x hx
      exact ⟨hS.closure_eq.symm ▸ hs,hi⟩
    · exact Or.inr hs

theorem regular_set_occupies_a_side (S U K L R : Set X) (x : X)
    (hS : IsClosed S) (hregular : S ⊆ closure (interior S))
    (hU : IsOpen U) (hxS : x ∈ S) (hxU : x ∈ U)
    (hboundary : frontier S ∩ U = K)
    (hsides : U \ K = L ∪ R) (hL : IsPreconnected L) (hR : IsPreconnected R) :
    L ⊆ interior S ∨ R ⊆ interior S := by
  have avoid (Q : Set X) (hQ : Q ⊆ L ∪ R) : ∀ y ∈ Q, y ∉ frontier S := by
    intro y hy hfront
    have hyUK : y ∈ U \ K := by rw [hsides]; exact hQ hy
    exact hyUK.2 (hboundary ▸ ⟨hfront,hyUK.1⟩)
  have dl := preconnected_side_dichotomy S L hS hL (avoid L subset_union_left)
  have dr := preconnected_side_dichotomy S R hS hR (avoid R subset_union_right)
  obtain ⟨y,hyU,hyS⟩ := (mem_closure_iff_nhds.mp (hregular hxS)) U (hU.mem_nhds hxU)
  have hyK : y ∉ K := by
    intro hy
    rw [←hboundary] at hy
    exact hy.1.2 hyS
  have hyLR : y ∈ L ∪ R := by rw [←hsides]; exact ⟨hyU,hyK⟩
  rcases hyLR with hyL | hyR
  · left
    exact dl.resolve_right (fun h => h hyL (interior_subset hyS))
  · right
    exact dr.resolve_right (fun h => h hyR (interior_subset hyS))

/-- Two regular-closed bodies with a common local frontier and two connected
nonempty sides must occupy opposite sides under interior packing. Their union
contains the whole displayed neighborhood, so no third regular body can touch
its center without violating packing. -/
theorem paired_bodies_cover_two_sided_neighborhood (S T U K L R : Set X) (x : X)
    (hS : IsClosed S) (hT : IsClosed T)
    (hSregular : S ⊆ closure (interior S)) (hTregular : T ⊆ closure (interior T))
    (hU : IsOpen U) (hxS : x ∈ S) (hxT : x ∈ T) (hxU : x ∈ U)
    (hboundaryS : frontier S ∩ U = K) (hboundaryT : frontier T ∩ U = K)
    (hsides : U \ K = L ∪ R) (hL : IsConnected L) (hR : IsConnected R)
    (hpacking : Disjoint (interior S) (interior T)) : U ⊆ S ∪ T := by
  have os := regular_set_occupies_a_side S U K L R x hS hSregular hU hxS hxU
    hboundaryS hsides hL.isPreconnected hR.isPreconnected
  have ot := regular_set_occupies_a_side T U K L R x hT hTregular hU hxT hxU
    hboundaryT hsides hL.isPreconnected hR.isPreconnected
  have hK : K ⊆ S := by
    intro y hy
    rw [←hboundaryS] at hy
    exact hS.closure_eq ▸ hy.1.1
  have clash (Q : Set X) (hne : Q.Nonempty) (hs : Q ⊆ interior S) (ht : Q ⊆ interior T) : False := by
    obtain ⟨y,hy⟩ := hne
    exact disjoint_left.mp hpacking (hs hy) (ht hy)
  rcases os with sl | sr <;> rcases ot with tl | tr
  · exact (clash L hL.nonempty sl tl).elim
  · intro y hy
    by_cases hk : y ∈ K
    · exact Or.inl (hK hk)
    have hside : y ∈ L ∪ R := by rw [←hsides]; exact ⟨hy,hk⟩
    exact hside.elim (fun h => Or.inl (interior_subset (sl h)))
      (fun h => Or.inr (interior_subset (tr h)))
  · intro y hy
    by_cases hk : y ∈ K
    · exact Or.inl (hK hk)
    have hside : y ∈ L ∪ R := by rw [←hsides]; exact ⟨hy,hk⟩
    exact hside.elim (fun h => Or.inr (interior_subset (tl h)))
      (fun h => Or.inl (interior_subset (sr h)))
  · exact (clash R hR.nonempty sr tr).elim

end
end LiteralPlanar
