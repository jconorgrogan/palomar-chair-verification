module

public import ProductClosure.CompilerData
public import ProductClosure.ProductWorldProfiles

@[expose] public section

/-! Concrete repeatable product-world existence for the exact graph compiler. -/
namespace ProductClosure.CompilerData
open NativeCompiler ProductGraphSites ProductGraphExact ProductWorldProfiles
noncomputable section
variable {a b : ℕ}

/-- Two actual full-profile factor worlds construct a full-profile world for
the exact product compiler data, with its fixed native site ordering. -/
theorem prod_hasWorld (A : CompilerData a) (B : CompilerData b)
    (hA : A.HasWorld) (hB : B.HasWorld) : (A.prod B).HasWorld := by
  letI : LinearOrder (Site A.cells) := nativeSiteOrder (S := A.cells) A.dimension
  letI : LinearOrder (Site B.cells) := nativeSiteOrder (S := B.cells) B.dimension
  letI : LinearOrder (Site (nativeProduct A.cells B.cells)) :=
    nativeSiteOrder (S := nativeProduct A.cells B.cells) (A.prod B).dimension
  obtain ⟨WA, hWA⟩ := hA
  obtain ⟨WB, hWB⟩ := hB
  let cA : Polycube.Cell A.cells := ⟨A.nonempty.choose, A.nonempty.choose_spec⟩
  let cB : Polycube.Cell B.cells := ⟨B.nonempty.choose, B.nonempty.choose_spec⟩
  refine ⟨nativeProductWorld WA WB, ?_⟩
  exact nativeProductWorld_fullProfile A.generators B.generators A.proper B.proper
    cA cB WA WB hWA hWB

#print axioms prod_hasWorld
end
end ProductClosure.CompilerData
