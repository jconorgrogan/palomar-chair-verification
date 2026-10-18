module

public import ProductClosure.ProductGraphExact
public import ProductClosure.NativeProfileDefinitions

@[expose] public section

/-!
# Literal all-site full-profile pullback

This uses NativeCompiler.FullProfileMating itself. Neither a selected-site
approximation nor an assumed preservation certificate occurs in the theorem.
Every native product site is handled through the proved complete coproduct.
-/
namespace ProductClosure.ProductGraphFullProfiles
noncomputable section
open NativeCompiler PhysicalRegistration.ComponentCoefficients
open ProductGraph ProductGraphOrbit ProductGraphOrientation ProductGraphSites ProductGraphPlacements
open ProductGraphRightSites ProductGraphSiteCoproduct ProductGraphBinding
open ProductGraphExclusions ProductGraphCommonExclusions ProductGraphExact
variable {a b : ℕ}
variable {SA : Finset (Polycube.LatticeIndex (a+1))}
    {SB : Finset (Polycube.LatticeIndex (b+1))}
variable [LinearOrder (Site SA)] [LinearOrder (Site SB)] [LinearOrder (Site (nativeProduct SA SB))]

def canonicalPassive (a b : ℕ) : Passive a b :=
  passive (frameToBlock (Equiv.refl _, fun _ => true))

/-- Each factor all-site equation lifts to every product site, and any one
occupied passive cell recovers every factor equation. -/
theorem fullProfile_liftLeft_iff (A : Finset (Space a ≃ᵢ Space a))
    (B : Finset (Space b ≃ᵢ Space b))
    (hA : ∀ g ∈ A, IsProperPlacement g) (hB : ∀ g ∈ B, IsProperPlacement g)
    (c₀ : Polycube.Cell SB) (g : Space a ≃ᵢ Space a) :
    FullProfileMating (graphCoefficients (actualProductGraph (SA := SA) (SB := SB) A B hA hB))
      (liftLeft g) ↔ FullProfileMating (graphCoefficients (contactGraph (S := SA) A hA)) g := by
  constructor
  · intro hp u v ht
    let p := canonicalPassive a (b+1)
    have hh := hp (leftSite u c₀ p) (leftSite v c₀ p) (SiteTransport_liftLeft g u v c₀ p ht)
    exact ((actual_value_left_iff A B hA hB u v c₀ c₀ p p).mp hh).2.2
  · intro hf U V ht
    obtain ⟨u,rfl⟩ := (siteCoproductEquiv SA SB).surjective U
    obtain ⟨v,rfl⟩ := (siteCoproductEquiv SA SB).surjective V
    rcases u with ⟨u,c,p⟩ | ⟨u,c,p⟩ <;> rcases v with ⟨v,d,q⟩ | ⟨v,d,q⟩
    · simp only [siteCoproductEquiv_left] at ht ⊢
      obtain ⟨h,rfl,rfl⟩ := (SiteTransport_liftLeft_iff g u v c d p q).mp ht
      exact (actual_value_left_iff A B hA hB u v c c p p).mpr ⟨rfl,rfl,hf u v h⟩
    · simp only [siteCoproductEquiv_left, siteCoproductEquiv_right,
        commonRightSite_eq_rightRawSite] at ht
      exact (no_left_transport_left_right g u c p d v.1 (rightCommonFrameEquiv (v.2,q)) ht).elim
    · simp only [siteCoproductEquiv_left, siteCoproductEquiv_right,
        commonRightSite_eq_rightRawSite] at ht
      exact (no_left_transport_right_left g v d q c u.1 (rightCommonFrameEquiv (u.2,p)) ht).elim
    · simp only [siteCoproductEquiv_right, commonRightSite_eq_rightRawSite] at ht
      exact (no_left_transport_right_right g c d u.1 v.1
        (rightCommonFrameEquiv (u.2,p)) (rightCommonFrameEquiv (v.2,q)) ht).elim

/-- The symmetric B-factor theorem uses the actual common-dimension placement
and its separately proved native right-factor orientation twist. -/
theorem fullProfile_liftRight_iff (A : Finset (Space a ≃ᵢ Space a))
    (B : Finset (Space b ≃ᵢ Space b))
    (hA : ∀ g ∈ A, IsProperPlacement g) (hB : ∀ g ∈ B, IsProperPlacement g)
    (c₀ : Polycube.Cell SA) (g : Space b ≃ᵢ Space b) :
    FullProfileMating (graphCoefficients (actualProductGraph (SA := SA) (SB := SB) A B hA hB))
      (commonLiftRight g) ↔ FullProfileMating (graphCoefficients (contactGraph (S := SB) B hB)) g := by
  constructor
  · intro hp u v ht
    let p := canonicalPassive b (a+1)
    have htrans := (SiteTransport_commonLiftRight_iff g u v c₀ c₀ p p).mpr ⟨ht,rfl,rfl⟩
    have hh := hp (commonRightSite u c₀ p) (commonRightSite v c₀ p) htrans
    exact ((actual_value_right_iff A B hA hB u v c₀ c₀ p p).mp hh).2.2
  · intro hf U V ht
    obtain ⟨u,rfl⟩ := (siteCoproductEquiv SA SB).surjective U
    obtain ⟨v,rfl⟩ := (siteCoproductEquiv SA SB).surjective V
    rcases u with ⟨u,c,p⟩ | ⟨u,c,p⟩ <;> rcases v with ⟨v,d,q⟩ | ⟨v,d,q⟩
    · simp only [siteCoproductEquiv_left] at ht
      exact (no_right_transport_left_left g u v c d p q ht).elim
    · simp only [siteCoproductEquiv_left, siteCoproductEquiv_right] at ht
      exact (no_right_transport_left_right g u c p v d q ht).elim
    · simp only [siteCoproductEquiv_left, siteCoproductEquiv_right] at ht
      exact (no_right_transport_right_left g v d q u c p ht).elim
    · simp only [siteCoproductEquiv_right] at ht ⊢
      obtain ⟨h,rfl,rfl⟩ := (SiteTransport_commonLiftRight_iff g u v c d p q).mp ht
      exact (actual_value_right_iff A B hA hB u v c c p p).mpr ⟨rfl,rfl,hf u v h⟩

/-- No literal opposite coefficient can join the two native facet types. -/
theorem actual_value_no_cross (A : Finset (Space a ≃ᵢ Space a))
    (B : Finset (Space b ≃ᵢ Space b))
    (hA : ∀ g ∈ A, IsProperPlacement g) (hB : ∀ g ∈ B, IsProperPlacement g)
    (u : Site SA) (c : Polycube.Cell SB) (p : Passive a (b+1))
    (v : Site SB) (d : Polycube.Cell SA) (q : Passive b (a+1)) :
    value (actualProductGraph A B hA hB) orientation (commonRightSite v d q) ≠
      -value (actualProductGraph A B hA hB) orientation (leftSite u c p) := by
  intro he
  have hr := ((opposite_value_iff _ _ orientation_sign _ _).mp he).1
  have hiso := @SimpleGraph.Iso.reachable_iff _ _ _ _ (actualGraphIso (SA := SA) (SB := SB) A B hA hB)
    (.inl (u,c,p)) (.inr (v,d,q))
  change (actualProductGraph A B hA hB).Reachable
    (siteCoproductEquiv SA SB (.inl (u,c,p))) (siteCoproductEquiv SA SB (.inr (v,d,q))) ↔ _ at hiso
  rw [siteCoproductEquiv_left, siteCoproductEquiv_right] at hiso
  exact not_sum_reachable_cross _ _ _ _ (hiso.mp hr)

#print axioms fullProfile_liftLeft_iff
#print axioms fullProfile_liftRight_iff
#print axioms actual_value_no_cross
end
end ProductClosure.ProductGraphFullProfiles
