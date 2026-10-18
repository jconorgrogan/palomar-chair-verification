module

public import SparseMonotiles.ContactIndexedChecker
public import ProductClosure.ChairFacetBridge
public import ProductClosure.NativePrescribedOrbit

@[expose] public section

/-! Exact finite indexed CLARK carrier facets and literal dense native facets.
The interface retains actual integer planes, occupied cells and orientations. -/
namespace ClarkSeed.NativeFacets
open ProductClosure
noncomputable section

variable {d : ℕ} {S : Finset (Polycube.LatticeIndex d)}

def toContact (f : Polycube.Facet S) : SparseMonotiles.Contact.Facet d :=
  ⟨f.cell.val,f.axis,f.positive⟩

theorem toContact_injective : Function.Injective (@toContact d S) := by
  intro f g h
  apply Polycube.Facet.ext
  · exact Subtype.ext (congrArg SparseMonotiles.Contact.Facet.cell h)
  · exact congrArg SparseMonotiles.Contact.Facet.axis h
  · exact congrArg SparseMonotiles.Contact.Facet.positive h

theorem centre2_cast (f : Polycube.Facet S) (i : Fin d) :
    ((toContact f).centre2 i : ℝ) = 2 * Polycube.facetCenter f i := by
  by_cases hi : i = f.axis
  · subst i
    cases hp : f.positive <;>
      simp [toContact, SparseMonotiles.Contact.Facet.centre2,
        SparseMonotiles.Contact.Facet.normal, Polycube.facetCenter,
        Polycube.latticeCenter, Polycube.sign, hp] <;> ring
  · simp [toContact, SparseMonotiles.Contact.Facet.centre2, hi,
      Polycube.facetCenter_tangent f i hi]
    ring

end
end ClarkSeed.NativeFacets
