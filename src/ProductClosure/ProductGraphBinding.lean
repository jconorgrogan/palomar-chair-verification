module

public import ProductClosure.ProductGraphExclusions
public import ProductClosure.ProductGraphComponents

@[expose] public section

/-! Literal native contact graphs of geometrically lifted factor languages. -/
namespace ProductClosure.ProductGraphBinding
noncomputable section
open ProductGraphSites ProductGraphOrbit ProductGraphPlacements ProductGraphExclusions NativeCompiler
attribute [local instance] Classical.propDecidable
variable {a b : ℕ}
variable {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)}

def leftLanguage (A : Finset (Space a ≃ᵢ Space a)) :
    Finset (Space (a+b) ≃ᵢ Space (a+b)) := A.image liftLeft

theorem leftLanguage_proper (A : Finset (Space a ≃ᵢ Space a))
    (hA : ∀ g ∈ A, IsProperPlacement g) :
    ∀ g ∈ leftLanguage (b := b) A, IsProperPlacement g := by
  intro g hmem
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hmem
  exact liftLeft_proper g (hA g hg)

/-- Exact adjacency for the actual compiler contact graph, not a synthetic
graph defined to be copies. Passive labels and factor transport are recovered. -/
theorem contactGraph_left_left (A : Finset (Space a ≃ᵢ Space a))
    (hA : ∀ g ∈ A, IsProperPlacement g)
    (u v : Site S) (c d : Polycube.Cell T) (p q : Passive a b) :
    (contactGraph (S := nativeProduct S T) (leftLanguage A) (leftLanguage_proper A hA)).Adj
      (leftSite u c p) (leftSite v d q) ↔
      (contactGraph A hA).Adj u v ∧ c = d ∧ p = q := by
  constructor
  · rintro ⟨g,hmem,ht⟩
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hmem
    rcases ht with ht | ht
    · obtain ⟨h,hd,hp⟩ := (SiteTransport_liftLeft_iff g u v c d p q).mp ht
      exact ⟨⟨g,hg,Or.inl h⟩,hd,hp⟩
    · obtain ⟨h,hd,hp⟩ := (SiteTransport_liftLeft_iff g v u d c q p).mp ht
      exact ⟨⟨g,hg,Or.inr h⟩,hd.symm,hp.symm⟩
  · rintro ⟨⟨g,hg,ht⟩,rfl,rfl⟩
    refine ⟨liftLeft g,Finset.mem_image.mpr ⟨g,hg,rfl⟩,?_⟩
    exact ht.elim
      (fun h => Or.inl (SiteTransport_liftLeft g u v c p h))
      (fun h => Or.inr (SiteTransport_liftLeft g v u c p h))

/-- The actual A language has no graph edges on B-type facets. -/
theorem contactGraph_no_left_right_right (A : Finset (Space a ≃ᵢ Space a))
    (hA : ∀ g ∈ A, IsProperPlacement g)
    (c d : Polycube.Cell S) (f h : Polycube.Facet T) (F H : Frame (a+b)) :
    ¬(contactGraph (S := nativeProduct S T) (leftLanguage A) (leftLanguage_proper A hA)).Adj
      (rightRawSite c f F) (rightRawSite d h H) := by
  rintro ⟨g,hmem,ht⟩
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hmem
  exact ht.elim (no_left_transport_right_right g c d f h F H)
    (no_left_transport_right_right g d c h f H F)

/-- The actual A language cannot make a graph edge change facet type. -/
theorem contactGraph_no_left_cross (A : Finset (Space a ≃ᵢ Space a))
    (hA : ∀ g ∈ A, IsProperPlacement g)
    (u : Site S) (c : Polycube.Cell T) (p : Passive a b)
    (d : Polycube.Cell S) (f : Polycube.Facet T) (F : Frame (a+b)) :
    ¬(contactGraph (S := nativeProduct S T) (leftLanguage A) (leftLanguage_proper A hA)).Adj
      (leftSite u c p) (rightRawSite d f F) := by
  rintro ⟨g,hmem,ht⟩
  obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hmem
  exact ht.elim (no_left_transport_left_right g u c p d f F)
    (no_left_transport_right_left g u c p d f F)

#print axioms contactGraph_left_left
#print axioms contactGraph_no_left_right_right
#print axioms contactGraph_no_left_cross
end
end ProductClosure.ProductGraphBinding
