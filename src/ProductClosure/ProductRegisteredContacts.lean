module

public import ProductClosure.ProductRegisteredPoses
public import ProductClosure.ProductGraphClosure
public import ProductClosure.PoseMaterialRealization
public import ProductClosure.ProductWorldSeparation

@[expose] public section

/-! The literal Euclidean F-closure is the exact registered relative
product language, with genuine carrier separation retained in each factor. -/
namespace ProductClosure.ProductRegisteredContacts
noncomputable section
open Set NativeCompiler ProductGraphSites ProductGraphPlacements ProductGraphSiteCoproduct
open ProductGraphExact ProductGraphClosure ProductGraphCarrierDisjoint ProductRegisteredPoses

/-- The factor mate predicate retains nonoverlap and actual contact as well
as every compiled profile equation. -/
def RegisteredMate {m : ℕ} (S : Finset (Polycube.LatticeIndex (m+1))) [LinearOrder (Site S)]
    (E : Finset (Space m ≃ᵢ Space m)) (hE : ∀ g ∈ E, IsProperPlacement g)
    (q : RegisteredPrime.Pose (m+1)) : Prop :=
  PhysicalRegistration.NativeChair.poseIsometry q ∈ denseContactClosure (S := S) E hE

theorem RegisteredMate.fullProfile {m : ℕ} {S : Finset (Polycube.LatticeIndex (m+1))}
    [LinearOrder (Site S)] {E : Finset (Space m ≃ᵢ Space m)}
    {hE : ∀ g ∈ E, IsProperPlacement g} {q : RegisteredPrime.Pose (m+1)}
    (h : RegisteredMate S E hE q) :
    FullProfileMating (graphCoefficients (contactGraph (S := S) E hE))
      (PhysicalRegistration.NativeChair.poseIsometry q) := h.1

/-- Real carrier separation of a relative pose gives disjoint actual cell
footprints in every world chart. -/
theorem registeredMate_separates {m : ℕ} (S : Finset (Polycube.LatticeIndex (m+1)))
    [LinearOrder (Site S)] (E : Finset (Space m ≃ᵢ Space m))
    (hE : ∀ g ∈ E, IsProperPlacement g) :
    World.Separates (World.placedCells S) (fun q r => RegisteredMate S E hE (q.relative r)) := by
  exact World.separates_of_relative_carrier S (fun _ he => he.2.2)

variable {a b : ℕ}
variable {SA : Finset (Polycube.LatticeIndex (a+1))}
    {SB : Finset (Polycube.LatticeIndex (b+1))}
variable [LinearOrder (Site SA)] [LinearOrder (Site SB)] [LinearOrder (Site (nativeProduct SA SB))]

/-- Exact registered form of physical product contact closure. The full
passive pose is identity; active factor registration is proved from the
recovered native contact rather than assumed of its arbitrary isometry. -/
theorem registered_product_mate_language
    (A : Finset (Space a ≃ᵢ Space a)) (B : Finset (Space b ≃ᵢ Space b))
    (hA : ∀ g ∈ A, IsProperPlacement g) (hB : ∀ g ∈ B, IsProperPlacement g)
    (hSA : SA.Nonempty) (hSB : SB.Nonempty)
    (q : RegisteredPrime.Pose ((a+1)+(b+1)))
    (hfull : FullProfileMating (graphCoefficients (actualProductGraph (SA := SA) (SB := SB) A B hA hB))
      (PhysicalRegistration.NativeChair.poseIsometry (World.castPose (productDim a (b+1)) q)))
    (hsite : ∃ u v : Site (nativeProduct SA SB), SiteTransport
      (PhysicalRegistration.NativeChair.poseIsometry (World.castPose (productDim a (b+1)) q)) u v)
    (hdisjoint : CarrierDisjoint (nativeProduct SA SB)
      (PhysicalRegistration.NativeChair.poseIsometry (World.castPose (productDim a (b+1)) q))) :
    World.RelativeProductLanguage (RegisteredMate SA A hA) (RegisteredMate SB B hB) q := by
  have hg : PhysicalRegistration.NativeChair.poseIsometry (World.castPose (productDim a (b+1)) q) ∈
      denseContactClosure (S := nativeProduct SA SB) (productLanguage A B)
        (productLanguage_proper A B hA hB) := ⟨hfull,hsite,hdisjoint⟩
  rw [exact_product_closure A B hA hB hSA hSB] at hg
  rcases hg with ⟨gA,hgA,he⟩ | ⟨gB,hgB,he⟩
  · obtain ⟨u,v,ht⟩ := hgA.2.1
    obtain ⟨qA,hgEq,hq⟩ := registeredPose_eq_leftBlock q gA u v ht he.symm
    rw [hq]
    refine ⟨World.blockPose_preservesBlocks _ _, Or.inl ⟨?_, ?_⟩⟩
    · simpa only [World.leftPose_blockPose, RegisteredMate, ← hgEq] using hgA
    · exact World.rightPose_blockPose _ _
  · obtain ⟨u,v,ht⟩ := hgB.2.1
    obtain ⟨qB,hgEq,hq⟩ := registeredPose_eq_rightBlock q gB u v ht he.symm
    rw [hq]
    refine ⟨World.blockPose_preservesBlocks _ _, Or.inr ⟨?_, ?_⟩⟩
    · exact World.leftPose_blockPose _ _
    · simpa only [World.rightPose_blockPose, RegisteredMate, ← hgEq] using hgB

#print axioms registeredMate_separates
#print axioms registered_product_mate_language
end
end ProductClosure.ProductRegisteredContacts
