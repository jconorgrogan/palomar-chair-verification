module

public import ProductClosure.ProductGraphFullProfiles
public import ProductClosure.ProductGraphContactWalks
public import ProductClosure.ProductGraphTransport

@[expose] public section

/-!
# No block restriction on a candidate dense mate

An arbitrary ambient isometry with a single actual matched full native site
and all literal compiled coefficient equations is proved to be exactly a
factor lift. The proof reconstructs an odd generator path in the factor and
uses whole-frame affine uniqueness. Passive translations, frame changes, and
mixed block rotations are excluded as conclusions.
-/
namespace ProductClosure.ProductGraphCandidateClosure
noncomputable section
open NativeCompiler PhysicalRegistration.ComponentCoefficients
open ProductGraphSites ProductGraphOrbit ProductGraphPlacements ProductGraphSiteCoproduct
open ProductGraphExact ProductGraphFullProfiles ProductGraphContactWalks ProductGraphTransport
variable {a b : ℕ}
variable {SA : Finset (Polycube.LatticeIndex (a+1))}
    {SB : Finset (Polycube.LatticeIndex (b+1))}

/-- Whole native transport between the same ordered sites fixes the entire
actual Euclidean isometry. -/
theorem isometry_eq_of_siteTransport {m : ℕ}
    {S : Finset (Polycube.LatticeIndex (m+1))} {u v : Site S}
    {g h : Space m ≃ᵢ Space m} (hg : SiteTransport g u v) (hh : SiteTransport h u v) : g = h := by
  have he := pose_eq_of_native_frame v
    g.toRealAffineIsometryEquiv.toAffineEquiv h.toRealAffineIsometryEquiv.toAffineEquiv
    (fun j => (hg.1 j).trans (hh.1 j).symm) (hg.2.1.trans hh.2.1.symm) (hg.2.2.trans hh.2.2.symm)
  apply IsometryEquiv.ext
  intro x
  exact congrArg (fun e : Pose m => e x) he

variable [LinearOrder (Site SA)] [LinearOrder (Site SB)] [LinearOrder (Site (nativeProduct SA SB))]

theorem candidate_factor_lift
    (A : Finset (Space a ≃ᵢ Space a)) (B : Finset (Space b ≃ᵢ Space b))
    (hA : ∀ g ∈ A, IsProperPlacement g) (hB : ∀ g ∈ B, IsProperPlacement g)
    (g : Space (a+(b+1)) ≃ᵢ Space (a+(b+1)))
    (hfull : FullProfileMating (graphCoefficients (actualProductGraph (SA := SA) (SB := SB) A B hA hB)) g)
    (hsite : ∃ u v : Site (nativeProduct SA SB), SiteTransport g u v) :
    (∃ gA : Space a ≃ᵢ Space a, g = liftLeft gA ∧ IsProperPlacement gA ∧
      FullProfileMating (graphCoefficients (contactGraph (S := SA) A hA)) gA ∧
        ∃ u v : Site SA, SiteTransport gA u v) ∨
    (∃ gB : Space b ≃ᵢ Space b, g = commonLiftRight gB ∧ IsProperPlacement gB ∧
      FullProfileMating (graphCoefficients (contactGraph (S := SB) B hB)) gB ∧
        ∃ u v : Site SB, SiteTransport gB u v) := by
  obtain ⟨U,V,ht⟩ := hsite
  obtain ⟨u,rfl⟩ := (siteCoproductEquiv SA SB).surjective U
  obtain ⟨v,rfl⟩ := (siteCoproductEquiv SA SB).surjective V
  have hcoeff := hfull _ _ ht
  rcases u with ⟨u,c,p⟩ | ⟨u,c,p⟩ <;> rcases v with ⟨v,d,q⟩ | ⟨v,d,q⟩
  · simp only [siteCoproductEquiv_left] at ht hcoeff
    obtain ⟨rfl,rfl,hfactor⟩ := (actual_value_left_iff A B hA hB u v c d p q).mp hcoeff
    obtain ⟨gA,hAtrans,hAproper⟩ := opposite_coefficients_exists_transport A hA u v hfactor
    have he : g = liftLeft gA :=
      isometry_eq_of_siteTransport ht (SiteTransport_liftLeft gA u v c p hAtrans)
    refine Or.inl ⟨gA,he,hAproper,?_,u,v,hAtrans⟩
    apply (fullProfile_liftLeft_iff A B hA hB c gA).mp
    rw [← he]
    exact hfull
  · simp only [siteCoproductEquiv_left, siteCoproductEquiv_right] at hcoeff
    exact (actual_value_no_cross A B hA hB u c p v d q hcoeff).elim
  · simp only [siteCoproductEquiv_left, siteCoproductEquiv_right] at hcoeff
    have he : value (actualProductGraph A B hA hB) orientation (commonRightSite u c p) =
        -value (actualProductGraph A B hA hB) orientation (leftSite v d q) := by
      change value _ orientation _ = -value _ orientation _ at hcoeff
      omega
    exact (actual_value_no_cross A B hA hB v d q u c p he).elim
  · simp only [siteCoproductEquiv_right] at ht hcoeff
    obtain ⟨rfl,rfl,hfactor⟩ := (actual_value_right_iff A B hA hB u v c d p q).mp hcoeff
    obtain ⟨gB,hBtrans,hBproper⟩ := opposite_coefficients_exists_transport B hB u v hfactor
    have hLift := (SiteTransport_commonLiftRight_iff gB u v c c p p).mpr ⟨hBtrans,rfl,rfl⟩
    have he : g = commonLiftRight gB := isometry_eq_of_siteTransport ht hLift
    refine Or.inr ⟨gB,he,hBproper,?_,u,v,hBtrans⟩
    apply (fullProfile_liftRight_iff A B hA hB c gB).mp
    rw [← he]
    exact hfull

/-- Dense-contact closure before the independent carrier-nonoverlap filter.
The predicate is the actual FullProfileMating equation plus a genuine native
contact witness; it is not defined to be a product or a graph component. -/
def witnessedProfileLanguage {m : ℕ}
    {S : Finset (Polycube.LatticeIndex (m+1))} [LinearOrder (Site S)]
    (E : Finset (Space m ≃ᵢ Space m)) (hE : ∀ g ∈ E, IsProperPlacement g) :
    Set (Space m ≃ᵢ Space m) :=
  {g | FullProfileMating (graphCoefficients (contactGraph (S := S) E hE)) g ∧
    ∃ u v : Site S, SiteTransport g u v}

/-- Exact product closure for every actual native all-site equation and
actual matched-site witness. No block preservation is assumed for the left side. -/
theorem witnessed_product_closure
    (A : Finset (Space a ≃ᵢ Space a)) (B : Finset (Space b ≃ᵢ Space b))
    (hA : ∀ g ∈ A, IsProperPlacement g) (hB : ∀ g ∈ B, IsProperPlacement g)
    (cA : Polycube.Cell SA) (cB : Polycube.Cell SB) :
    witnessedProfileLanguage (S := nativeProduct SA SB) (productLanguage A B)
      (productLanguage_proper A B hA hB) =
      (liftLeft '' witnessedProfileLanguage (S := SA) A hA) ∪
      (commonLiftRight '' witnessedProfileLanguage (S := SB) B hB) := by
  ext g
  constructor
  · rintro ⟨hfull,hsite⟩
    rcases candidate_factor_lift A B hA hB g hfull hsite with
      ⟨gA,he,_,hf,hs⟩ | ⟨gB,he,_,hf,hs⟩
    · exact Or.inl ⟨gA,⟨hf,hs⟩,he.symm⟩
    · exact Or.inr ⟨gB,⟨hf,hs⟩,he.symm⟩
  · rintro (⟨gA,⟨hf,u,v,ht⟩,rfl⟩ | ⟨gB,⟨hf,u,v,ht⟩,rfl⟩)
    · exact ⟨(fullProfile_liftLeft_iff A B hA hB cB gA).mpr hf,
        leftSite u cB (canonicalPassive a (b+1)), leftSite v cB (canonicalPassive a (b+1)),
        SiteTransport_liftLeft gA u v cB (canonicalPassive a (b+1)) ht⟩
    · exact ⟨(fullProfile_liftRight_iff A B hA hB cA gB).mpr hf,
        commonRightSite u cA (canonicalPassive b (a+1)), commonRightSite v cA (canonicalPassive b (a+1)),
        (SiteTransport_commonLiftRight_iff gB u v cA cA
        (canonicalPassive b (a+1)) (canonicalPassive b (a+1))).mpr ⟨ht,rfl,rfl⟩⟩

#print axioms isometry_eq_of_siteTransport
#print axioms candidate_factor_lift
#print axioms witnessed_product_closure
end
end ProductClosure.ProductGraphCandidateClosure
