module

public import ProductClosure.ChairFacetBridge
public import ProductClosure.NativeComponentOrder
public import ProductClosure.NativeProfileDefinitions
public import ProductClosure.ProductGraphEquations
public import PrimeFacetClosure.RealizedFacetClosure

@[expose] public section

/-! Literal graph/coefficient-language agreement with the checked chair seed.
The component ranks need not have the same enumeration; all equations agree. -/
namespace ProductClosure.ChairBridge
noncomputable section
open PhysicalRegistration.ComponentCoefficients

@[simp] theorem siteEquiv_frameMatrix {m : ℕ} (u : PhysicalRegistration.NativeChair.Site m) :
    NativeCompiler.frameMatrix (siteEquiv m u) = PhysicalRegistration.NativeChair.frameMatrix u := by
  ext i j
  induction j using Fin.lastCases with
  | last => simp [NativeCompiler.frameMatrix, PhysicalRegistration.NativeChair.frameMatrix]
  | cast j => simp [NativeCompiler.frameMatrix, PhysicalRegistration.NativeChair.frameMatrix]

@[simp] theorem siteEquiv_orientation {m : ℕ} (u : PhysicalRegistration.NativeChair.Site m) :
    NativeCompiler.orientation (siteEquiv m u) = PhysicalRegistration.NativeChair.orientation u := by
  simp [NativeCompiler.orientation, PhysicalRegistration.NativeChair.orientation]

@[simp] theorem siteEquiv_transport {m : ℕ} (g : NativeCompiler.Space m ≃ᵢ NativeCompiler.Space m)
    (u v : PhysicalRegistration.NativeChair.Site m) :
    NativeCompiler.SiteTransport g (siteEquiv m u) (siteEquiv m v) ↔
      PhysicalRegistration.NativeChair.SiteTransport g u v := by
  simp [NativeCompiler.SiteTransport, PhysicalRegistration.NativeChair.SiteTransport,
    NativeCompiler.placedNormal, PhysicalRegistration.NativeChair.placedNormal]

/-- Same literal generator isometries, same exact site equations. -/
def contactGraphIso {m : ℕ} (A : Finset (NativeCompiler.Space m ≃ᵢ NativeCompiler.Space m))
    (hA : ∀ g ∈ A, NativeCompiler.IsProperPlacement g) :
    PhysicalRegistration.NativeChair.contactGraph A hA ≃g
      NativeCompiler.contactGraph (S := cells m) A hA where
  toEquiv := siteEquiv m
  map_rel_iff' := by
    intro u v
    change (∃ g ∈ A, NativeCompiler.SiteTransport g (siteEquiv m u) (siteEquiv m v) ∨
      NativeCompiler.SiteTransport g (siteEquiv m v) (siteEquiv m u)) ↔ _
    simp only [siteEquiv_transport]
    rfl

theorem compiled_opposition_iff {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (NativeCompiler.Space m ≃ᵢ NativeCompiler.Space m))
    (hA : ∀ g ∈ A, NativeCompiler.IsProperPlacement g)
    (u v : PhysicalRegistration.NativeChair.Site m) :
    (NativeCompiler.compiledCoefficients (S := cells m) hm A hA).value (siteEquiv m v) =
      -(NativeCompiler.compiledCoefficients (S := cells m) hm A hA).value (siteEquiv m u) ↔
    (PhysicalRegistration.NativeChair.compiledCoefficients hm A hA).value v =
      -(PhysicalRegistration.NativeChair.compiledCoefficients hm A hA).value u := by
  letI := NativeCompiler.nativeSiteOrder (S := cells m) hm
  letI := PhysicalRegistration.NativeChair.nativeSiteOrder hm
  exact ProductGraph.coefficient_opposition_reindex _ _ (contactGraphIso A hA)
    _ _ PhysicalRegistration.NativeChair.orientation_sign NativeCompiler.orientation_sign
    (by
      intro u v
      change NativeCompiler.orientation (siteEquiv m v) = -NativeCompiler.orientation (siteEquiv m u) ↔ _
      rw [siteEquiv_orientation, siteEquiv_orientation]) u v

theorem compiled_fullProfile_iff {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (NativeCompiler.Space m ≃ᵢ NativeCompiler.Space m))
    (hA : ∀ g ∈ A, NativeCompiler.IsProperPlacement g)
    (g : NativeCompiler.Space m ≃ᵢ NativeCompiler.Space m) :
    NativeCompiler.FullProfileMating (NativeCompiler.compiledCoefficients (S := cells m) hm A hA) g ↔
      PhysicalRegistration.NativeChair.FullProfileMating
        (PhysicalRegistration.NativeChair.compiledCoefficients hm A hA) g := by
  constructor
  · intro h u v ht
    exact (compiled_opposition_iff hm A hA u v).mp
      (h _ _ ((siteEquiv_transport g u v).mpr ht))
  · intro h u v ht
    obtain ⟨u,rfl⟩ := (siteEquiv m).surjective u
    obtain ⟨v,rfl⟩ := (siteEquiv m).surjective v
    exact (compiled_opposition_iff hm A hA u v).mpr
      (h u v ((siteEquiv_transport g u v).mp ht))

end
end ProductClosure.ChairBridge
