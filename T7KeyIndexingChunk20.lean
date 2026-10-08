module
public import T7KeyIndexingBase
@[expose] public section
namespace SparseMonotiles.Contact.T7KeyIndexing
open IndexedData7 RootZeroPilot7
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem indexBindingChunk20 : ∀ j : Fin 32, IndexBinding ⟨640 + j.val, by omega⟩ := by decide +kernel
#print axioms indexBindingChunk20
end SparseMonotiles.Contact.T7KeyIndexing
