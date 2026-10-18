module

public import ClarkSeed.PoseAdapter
public import SparseMonotiles.CarrierHierarchyCatalog5
public import PhysicalRegistration.RegisteredPoseProperness
public import ProductClosure.NativeGraphCoefficients

@[expose] public section

/-! The exact recovered 284-pose catalog as finite actual Euclidean generator
input. Positive determinant is kernel-checked from the explicit signed rows;
no saved JSON result or profile-language closure is an assumption. -/
namespace ClarkSeed.Generators
noncomputable section
open SparseMonotiles ProductClosure.NativeCompiler PoseAdapter
open PhysicalRegistration.NativeChair

/-- A finite integer determinant computation on the actual recovered pose. -/
def determinantSign (p : Contact.Pose 5) : ℤ :=
  Uniform.permSign 5 (toRegistered p).frame.toUniform.perm *
    Uniform.signProd 5 (toRegistered p).frame.toUniform.neg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All 284 literal catalog rows pass ordinary kernel reduction. -/
theorem catalog_signs_checked :
    CarrierHierarchy.Catalog5.supplied.all (fun p => decide (determinantSign p = 1)) = true := by
  decide

theorem determinantSign_eq_one (p : Contact.Pose 5)
    (hp : p ∈ CarrierHierarchy.Catalog5.supplied) : determinantSign p = 1 := by
  have h := List.all_eq_true.mp catalog_signs_checked p hp
  exact of_decide_eq_true h

theorem catalog_frame_proper (p : Contact.Pose 5)
    (hp : p ∈ CarrierHierarchy.Catalog5.supplied) : (toRegistered p).frame.IsProper := by
  refine ⟨registered_toUniform_isPermOn (toRegistered p).frame, ?_⟩
  exact determinantSign_eq_one p hp

/-- The Euclidean realization of one original pose. -/
def realize (p : Contact.Pose 5) : ProductClosure.NativeCompiler.Space 4 ≃ᵢ ProductClosure.NativeCompiler.Space 4 :=
  poseIsometry (toRegistered p)

theorem realize_injective : Function.Injective realize := by
  intro p q h
  exact toRegistered_injective (poseIsometry_injective h)

/-- No augmentation or sampled subcatalog: exactly the recovered finite set. -/
def generators : Finset (ProductClosure.NativeCompiler.Space 4 ≃ᵢ ProductClosure.NativeCompiler.Space 4) := by
  classical
  exact CarrierHierarchy.Catalog5.supplied.toFinset.image realize

theorem mem_generators (g : ProductClosure.NativeCompiler.Space 4 ≃ᵢ ProductClosure.NativeCompiler.Space 4) :
    g ∈ generators ↔ ∃ p ∈ CarrierHierarchy.Catalog5.supplied, realize p = g := by
  classical
  simp [generators]

@[simp] theorem realize_mem_generators (p : Contact.Pose 5) :
    realize p ∈ generators ↔ p ∈ CarrierHierarchy.Catalog5.supplied := by
  rw [mem_generators]
  constructor
  · rintro ⟨q,hq,he⟩
    exact realize_injective he ▸ hq
  · intro hp
    exact ⟨p,hp,rfl⟩

theorem generators_proper (g : ProductClosure.NativeCompiler.Space 4 ≃ᵢ ProductClosure.NativeCompiler.Space 4) (hg : g ∈ generators) :
    ProductClosure.NativeCompiler.IsProperPlacement g := by
  obtain ⟨p,hp,rfl⟩ := (mem_generators g).mp hg
  exact (poseIsometry_isProper_iff (toRegistered p)).mpr (catalog_frame_proper p hp)

#print axioms catalog_signs_checked
#print axioms catalog_frame_proper
#print axioms generators_proper
end
end ClarkSeed.Generators
