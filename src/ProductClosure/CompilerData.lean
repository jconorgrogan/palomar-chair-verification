module

public import ProductClosure.ChairSeedWorld
public import ProductClosure.NativeProfileSelf
public import ProductClosure.WorldProfileContacts
public import ProductClosure.ProductGraphExact

@[expose] public section

/-! Repeatable concrete compiler data. The record contains only actual finite
geometry and finite proper generators. Existence and aperiodicity are separate
proved propositions, never fields smuggling in a product-closure conclusion. -/
namespace ProductClosure
open Set
noncomputable section

structure CompilerData (m : ℕ) where
  cells : Finset (Polycube.LatticeIndex (m+1))
  nonempty : cells.Nonempty
  dimension : 2 ≤ m
  generators : Finset (NativeCompiler.Space m ≃ᵢ NativeCompiler.Space m)
  proper : ∀ g ∈ generators, NativeCompiler.IsProperPlacement g

namespace CompilerData
variable {m : ℕ}

def coefficients (D : CompilerData m) :=
  NativeCompiler.compiledCoefficients (S := D.cells) D.dimension D.generators D.proper

def ProfileLanguage (D : CompilerData m) (q r : RegisteredPrime.Pose (m+1)) : Prop :=
  NativeCompiler.FullProfileMating D.coefficients
    (PhysicalRegistration.NativeChair.poseIsometry (q.relative r))

def HasWorld (D : CompilerData m) : Prop :=
  ∃ W : World.CompleteTiling (World.placedCells D.cells),
    NativeCompiler.CellWorldFullProfile D.coefficients W

/-- Universal aperiodicity of the literal full-profile cell worlds. -/
def PeriodFree (D : CompilerData m) : Prop :=
  ∀ W : World.CompleteTiling (World.placedCells D.cells),
    W.IsLegal World.LatticeAdjacent D.ProfileLanguage →
    ∀ v, W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate v) → v = 0

def material (D : CompilerData m) : Set (NativeCompiler.Space m) :=
  letI : NeZero m := ⟨by have := D.dimension; omega⟩
  NativeCompiler.body D.coefficients

/-- Once separately proved algebraic world facts are supplied, the body is
an actual unrestricted-isometry physical aperiodic monotile with interior. -/
theorem physical_monotile (D : CompilerData m) (hW : D.HasWorld) (hzero : D.PeriodFree) :
    (interior D.material).Nonempty ∧
      SparseMonotiles.IsAperiodicMonotile D.material := by
  letI : NeZero m := ⟨by have := D.dimension; omega⟩
  letI : Nonempty (Polycube.Cell D.cells) :=
    ⟨⟨D.nonempty.choose,D.nonempty.choose_spec⟩⟩
  obtain ⟨W,hw⟩ := hW
  apply NativeCompiler.body_nonemptyInterior_aperiodicMonotile_of_profile_worlds D.dimension
    D.coefficients W hw
  intro V hV v hv
  apply hzero V _ v hv
  intro x y _ _
  exact hV _ _ (V.owner_mem x) (V.owner_mem y)

/-- The exact previously checked chair generator family is concrete compiler
input. Its source dependency is explicit, including primality and residue. -/
def chair (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3) : CompilerData m where
  cells := ChairBridge.cells m
  nonempty := ChairBridge.cells_nonempty m
  dimension := PhysicalRegistration.NativeChair.GeneratedCompiler.nativeDimension_ge_two hmod
  generators := PhysicalRegistration.NativeChair.GeneratedCompiler.generators hp hmod
  proper := PhysicalRegistration.NativeChair.GeneratedCompiler.generators_proper hp hmod

theorem chair_hasWorld (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3) :
    (chair hp hmod).HasWorld := by
  obtain ⟨W,hW⟩ := ChairBridge.seed_world_exists hp hmod
  refine ⟨W, NativeCompiler.CellWorldFullProfile_of_distinct _ W ?_⟩
  intro q r hq hr hne
  exact hW q hq r hr hne

theorem chair_periodFree (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3) :
    (chair hp hmod).PeriodFree :=
  ChairBridge.seed_world_statePeriod_zero hp hmod

/-- Actual Cartesian carrier and union of the two actual lifted finite
generator languages. Product profile closure is proved separately. -/
def prod {a b : ℕ} (A : CompilerData a) (B : CompilerData b) : CompilerData (a+(b+1)) where
  cells := ProductGraphSites.nativeProduct A.cells B.cells
  nonempty := by
    obtain ⟨z,hz⟩ := Polycube.productCells_nonempty A.nonempty B.nonempty
    exact ⟨Polycube.castIndex (ProductGraphSites.productDim a (b+1)) z,
      (Polycube.castIndex_mem_castCells _ _ _).mpr hz⟩
  dimension := by have := A.dimension; omega
  generators := ProductGraphExact.productLanguage A.generators B.generators
  proper := ProductGraphExact.productLanguage_proper A.generators B.generators A.proper B.proper

end CompilerData
end
end ProductClosure
