module
public import T7KeyIndexingBindings
public import GeneratorKeyIndexingCoverage
public import PilotClassifier
@[expose] public section
namespace SparseMonotiles.Contact.T7KeyIndexing
open IndexedData7 RootZeroPilot7
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem facet_eq_sourceOwner : generatorIndexingT7.facet = sourceOwner := rfl

theorem key_eq_sourceKey : generatorIndexingT7.key = sourceKey := rfl

theorem profileIndices_eq (i : Fin 896) :
    generatorIndexingT7.profileIndices i = (profileList i).toFinset := rfl

/-- Every key occurring in an original facet profile has its exact owner
and key value represented by this flat indexing. -/
theorem covers_profile {i : Fin 896} {k : BoxKey 7}
    (hk : k ∈ geometry.profile i) :
    ∃ a : Fin 1024, sourceOwner a = i ∧ sourceKey a = k :=
  generatorIndexingT7.covers hk

/-- Reuse the checked root-zero source facts; no root-dependent recomputation. -/
theorem source_mem_profile (a : Fin 1024) :
    generatorIndexingT7.key a ∈ geometry.profile (generatorIndexingT7.facet a) :=
  RootZeroPilot7.all_source a

/-- Definitional identity with the original pairPose algorithm. -/
theorem pair_eq_original (a b : Fin 1024) :
    generatorIndexingT7.pair a b =
      pairPose geometry.denominator (geometry.facet (sourceOwner a))
        (geometry.facet (sourceOwner b)) (sourceKey a) (sourceKey b) := rfl

theorem pair_root_zero (b : Fin 1024) :
    generatorIndexingT7.pair 0 b = RootZeroPilot7.rootPair b := rfl

/-- Exact indexed-pair enumeration of generated candidates, without any
claim that those candidates belong to a checked replay table. -/
theorem generated_iff_pair (p : Pose 7) :
    p ∈ geometry.generatedCandidates ↔
      ∃ a b : Fin 1024, generatorIndexingT7.pair a b = some p :=
  generatorIndexingT7.mem_generatedCandidates_iff_exists_pair source_mem_profile p

#print axioms all_indexBinding
#print axioms all_profile_eq
#print axioms all_owner_checked
#print axioms generatorIndexingT7
#print axioms covers_profile
#print axioms source_mem_profile
#print axioms pair_eq_original
#print axioms pair_root_zero
#print axioms generated_iff_pair
end SparseMonotiles.Contact.T7KeyIndexing
