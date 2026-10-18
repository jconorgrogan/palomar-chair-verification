module

public import ProductClosure.NativeGraphCoefficients
public import ProductClosure.SignedPermutationRegistration
public import ProductClosure.PlacedConicalGerms

@[expose] public section

/-! Full, unquotiented coefficient matching for literal finite-polycube sites. -/
namespace ProductClosure.NativeCompiler
noncomputable section
variable {m J : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

/-- All full-site transport equations, with no sampled sites or label quotient. -/
def FullProfileMating (a : Coefficients S J) (g : Space m ≃ᵢ Space m) : Prop :=
  ∀ u v : Site S, SiteTransport g u v → a.value v = -a.value u

end
end ProductClosure.NativeCompiler
