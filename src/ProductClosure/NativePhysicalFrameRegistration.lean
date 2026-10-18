module

public import ProductClosure.PhysicalKeyFrames
public import ProductClosure.SignedPermutationRegistration

@[expose] public section

namespace ProductClosure.NativeCompiler
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell S)]

/-- Every actual tile-key companion is integrally registered relative to its
root tile. All frame and center premises are supplied by the physical tiling. -/
theorem PhysicalTiling.exists_integrally_registered_companion
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site S) :
    ∃ iv : ι × Site S, iv.1 ≠ root ∧
      f root '' creaseComplex a u = f iv.1 '' creaseComplex a iv.2 ∧
      HasIntegralSignedPermutation (relativePlacement (f root) (f iv.1)) := by
  obtain ⟨iv, hiv, _⟩ := T.unique_framed_key_companion hm root u
  exact ⟨iv, hiv.1, hiv.2.1,
    relativePlacement_integral_signed_permutation u iv.2 (f root) (f iv.1)
      hiv.2.2.1 hiv.2.2.2.1 hiv.2.2.2.2.1⟩


end
end ProductClosure.NativeCompiler
