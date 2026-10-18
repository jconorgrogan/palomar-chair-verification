module

public import ClarkSeed.Generators
public import ClarkSeed.OddWalkProfiles
public import ProductClosure.CompilerData

@[expose] public section

/-! Concrete 5D finite compiler input, distinct from its pending world and
aperiodicity propositions. The generator set and positive determinants are
fully constructed; no old sparse-to-dense law is inserted as a record field. -/
namespace ClarkSeed
noncomputable section
open ProductClosure NativeCompiler

/-- The exact 31-cell native carrier and exact recovered 284-pose generator
language, realized as actual five-dimensional Euclidean isometries. -/
def compilerData : CompilerData 4 where
  cells := ChairBridge.cells 4
  nonempty := ChairBridge.cells_nonempty 4
  dimension := by decide
  generators := Generators.generators
  proper := Generators.generators_proper

@[simp] theorem compilerData_cells : compilerData.cells = ChairBridge.cells 4 := rfl
@[simp] theorem compilerData_generators : compilerData.generators = Generators.generators := rfl

/-- Each input generator satisfies every actual geometrically ordered native
coefficient equation by construction of the contact graph. -/
theorem compiled_generator_fullProfile {m : ℕ}
    {S : Finset (Polycube.LatticeIndex (m+1))} (hm : 2 ≤ m)
    (E : Finset (Space m ≃ᵢ Space m)) (hE : ∀ g ∈ E, IsProperPlacement g)
    (g : Space m ≃ᵢ Space m) (hg : g ∈ E) :
    FullProfileMating (compiledCoefficients (S := S) hm E hE) g := by
  intro u v ht
  exact compiledCoefficients_edge_neg hm E hE ⟨g,hg,Or.inl ht⟩

theorem compilerData_generator_fullProfile (p : SparseMonotiles.Contact.Pose 5)
    (hp : p ∈ SparseMonotiles.CarrierHierarchy.Catalog5.supplied) :
    FullProfileMating compilerData.coefficients (Generators.realize p) := by
  exact compiled_generator_fullProfile compilerData.dimension compilerData.generators
    compilerData.proper (Generators.realize p) ((Generators.realize_mem_generators p).mpr hp)

/-- Specialize odd-walk sparse preservation to the literal compiler's
geometric lexicographic ordering; no arbitrary component labels enter. -/
theorem compiled_fullProfile_sparse_profiles {m : ℕ}
    {S : Finset (Polycube.LatticeIndex (m+1))} (hm : 2 ≤ m)
    (E : Finset (Space m ≃ᵢ Space m)) (hE : ∀ g ∈ E, IsProperPlacement g)
    (P : Site S → ProfileMating.Profile (Space m))
    (hP : OddWalkProfiles.GeneratorProfiles E P) (g : Space m ≃ᵢ Space m)
    (hf : FullProfileMating (compiledCoefficients (S := S) hm E hE) g) :
    ∀ u v : Site S, SiteTransport g u v → P u = ProfileMating.mate g.toEquiv (P v) := by
  letI := nativeSiteOrder (S := S) hm
  exact OddWalkProfiles.fullProfile_sparse_profiles E hE P hP g hf

/-- The reusable sparse-profile consequence for this exact concrete input.
The original input-generator sparse law is a separate theorem to be bound
from the recovered checked facet catalog. -/
theorem compilerData_sparse_profiles
    (P : Site compilerData.cells → ProfileMating.Profile (Space 4))
    (hP : OddWalkProfiles.GeneratorProfiles compilerData.generators P)
    (g : Space 4 ≃ᵢ Space 4) (hf : FullProfileMating compilerData.coefficients g) :
    ∀ u v : Site compilerData.cells, SiteTransport g u v →
      P u = ProfileMating.mate g.toEquiv (P v) :=
  compiled_fullProfile_sparse_profiles compilerData.dimension compilerData.generators
    compilerData.proper P hP g hf

#print axioms compilerData
#print axioms compilerData_generator_fullProfile
#print axioms compiled_fullProfile_sparse_profiles
#print axioms compilerData_sparse_profiles
end
end ClarkSeed
