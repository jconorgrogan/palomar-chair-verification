module

public import ProductClosure.ProductGraphCandidateClosure
public import ProductClosure.ProductGraphCarrierDisjoint

@[expose] public section

/-!
# Exact physical native dense-contact product closure

`denseContactClosure` is defined directly from the literal finite compiler's
full-profile equations, an actual full native facet-site contact, and disjoint
physical carrier interiors. Candidate isometries are unrestricted. The main
set equality derives block preservation, every coefficient equation, and both
directions of carrier nonoverlap; none is a product-closure premise.
-/
namespace ProductClosure.ProductGraphClosure
noncomputable section
open NativeCompiler ProductGraphSites ProductGraphPlacements ProductGraphSiteCoproduct
open ProductGraphExact ProductGraphFullProfiles ProductGraphCandidateClosure ProductGraphCarrierDisjoint
variable {a b : ℕ}
variable {SA : Finset (Polycube.LatticeIndex (a+1))}
    {SB : Finset (Polycube.LatticeIndex (b+1))}

/-- The actual compiled dense-contact language: every full native site
coefficient equation, a genuine matched native site, and no carrier overlap. -/
def denseContactClosure {m : ℕ}
    {S : Finset (Polycube.LatticeIndex (m+1))} [LinearOrder (Site S)]
    (E : Finset (Space m ≃ᵢ Space m)) (hE : ∀ g ∈ E, IsProperPlacement g) :
    Set (Space m ≃ᵢ Space m) :=
  {g | FullProfileMating (graphCoefficients (contactGraph (S := S) E hE)) g ∧
    (∃ u v : Site S, SiteTransport g u v) ∧ CarrierDisjoint S g}

/-- Properness is forced by a real matched full site and its computed
opposite coefficients; the closure definition does not assume it. -/
theorem denseContactClosure_proper {m : ℕ}
    {S : Finset (Polycube.LatticeIndex (m+1))} [LinearOrder (Site S)]
    (E : Finset (Space m ≃ᵢ Space m)) (hE : ∀ g ∈ E, IsProperPlacement g)
    {g : Space m ≃ᵢ Space m} (hg : g ∈ denseContactClosure (S := S) E hE) :
    IsProperPlacement g := by
  obtain ⟨hfull,⟨u,v,ht⟩,_⟩ := hg
  exact (proper_and_connected_of_matched_coefficients (contactGraph E hE) g u v
    ht.1 ht.2.1 (hfull u v ht)).1

variable [LinearOrder (Site SA)] [LinearOrder (Site SB)] [LinearOrder (Site (nativeProduct SA SB))]

/-- Literal F_product(E_A square E_B) = F_A(E_A) square F_B(E_B),
including full-site profiles, actual contact, and carrier nonoverlap.
Only generator properness and nonempty finite factor carriers are assumed. -/
theorem exact_product_closure
    (A : Finset (Space a ≃ᵢ Space a)) (B : Finset (Space b ≃ᵢ Space b))
    (hA : ∀ g ∈ A, IsProperPlacement g) (hB : ∀ g ∈ B, IsProperPlacement g)
    (hSA : SA.Nonempty) (hSB : SB.Nonempty) :
    denseContactClosure (S := nativeProduct SA SB) (productLanguage A B)
      (productLanguage_proper A B hA hB) =
      (liftLeft '' denseContactClosure (S := SA) A hA) ∪
      (commonLiftRight '' denseContactClosure (S := SB) B hB) := by
  let cA : Polycube.Cell SA := ⟨hSA.choose,hSA.choose_spec⟩
  let cB : Polycube.Cell SB := ⟨hSB.choose,hSB.choose_spec⟩
  ext g
  constructor
  · rintro ⟨hfull,hsite,hdisjoint⟩
    rcases candidate_factor_lift A B hA hB g hfull hsite with
      ⟨gA,he,_,hf,hs⟩ | ⟨gB,he,_,hf,hs⟩
    · refine Or.inl ⟨gA,⟨hf,hs,?_⟩,he.symm⟩
      apply (carrierDisjoint_liftLeft_iff SA SB hSB gA).mp
      rwa [← he]
    · refine Or.inr ⟨gB,⟨hf,hs,?_⟩,he.symm⟩
      apply (carrierDisjoint_liftRight_iff SA SB hSA gB).mp
      rwa [← he]
  · rintro (⟨gA,⟨hf,⟨u,v,ht⟩,hd⟩,rfl⟩ | ⟨gB,⟨hf,⟨u,v,ht⟩,hd⟩,rfl⟩)
    · exact ⟨(fullProfile_liftLeft_iff A B hA hB cB gA).mpr hf,
        ⟨leftSite u cB (canonicalPassive a (b+1)), leftSite v cB (canonicalPassive a (b+1)),
          SiteTransport_liftLeft gA u v cB (canonicalPassive a (b+1)) ht⟩,
        (carrierDisjoint_liftLeft_iff SA SB hSB gA).mpr hd⟩
    · exact ⟨(fullProfile_liftRight_iff A B hA hB cA gB).mpr hf,
        ⟨commonRightSite u cA (canonicalPassive b (a+1)), commonRightSite v cA (canonicalPassive b (a+1)),
          (SiteTransport_commonLiftRight_iff gB u v cA cA
            (canonicalPassive b (a+1)) (canonicalPassive b (a+1))).mpr ⟨ht,rfl,rfl⟩⟩,
        (carrierDisjoint_liftRight_iff SA SB hSA gB).mpr hd⟩

/-- The eliminator used by complete-world decoding: every actual neighboring
product mate is exactly one factor mate, including its full profile and
physical nonoverlap. The other block is fixed pointwise as an entire pose. -/
theorem product_mate_decomposition
    (A : Finset (Space a ≃ᵢ Space a)) (B : Finset (Space b ≃ᵢ Space b))
    (hA : ∀ g ∈ A, IsProperPlacement g) (hB : ∀ g ∈ B, IsProperPlacement g)
    (hSA : SA.Nonempty) (hSB : SB.Nonempty)
    (g : Space (a+(b+1)) ≃ᵢ Space (a+(b+1)))
    (hfull : FullProfileMating (graphCoefficients (actualProductGraph (SA := SA) (SB := SB) A B hA hB)) g)
    (hsite : ∃ u v : Site (nativeProduct SA SB), SiteTransport g u v)
    (hdisjoint : CarrierDisjoint (nativeProduct SA SB) g) :
    (∃ gA : Space a ≃ᵢ Space a, g = liftLeft gA ∧
      FullProfileMating (graphCoefficients (contactGraph (S := SA) A hA)) gA ∧
        CarrierDisjoint SA gA ∧ IsProperPlacement gA) ∨
    (∃ gB : Space b ≃ᵢ Space b, g = commonLiftRight gB ∧
      FullProfileMating (graphCoefficients (contactGraph (S := SB) B hB)) gB ∧
        CarrierDisjoint SB gB ∧ IsProperPlacement gB) := by
  have hg : g ∈ denseContactClosure (S := nativeProduct SA SB) (productLanguage A B)
      (productLanguage_proper A B hA hB) := ⟨hfull,hsite,hdisjoint⟩
  rw [exact_product_closure A B hA hB hSA hSB] at hg
  rcases hg with ⟨gA,hAall,he⟩ | ⟨gB,hBall,he⟩
  · exact Or.inl ⟨gA,he.symm,hAall.1,hAall.2.2,denseContactClosure_proper A hA hAall⟩
  · exact Or.inr ⟨gB,he.symm,hBall.1,hBall.2.2,denseContactClosure_proper B hB hBall⟩

#print axioms denseContactClosure_proper
#print axioms exact_product_closure
#print axioms product_mate_decomposition
end
end ProductClosure.ProductGraphClosure
