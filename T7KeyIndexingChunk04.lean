module
public import T7KeyIndexingBase
@[expose] public section
namespace SparseMonotiles.Contact.T7KeyIndexing
open IndexedData7 RootZeroPilot7
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem indexBindingChunk04 : ∀ j : Fin 32, IndexBinding ⟨128 + j.val, by omega⟩ := by decide +kernel
#print axioms indexBindingChunk04
end SparseMonotiles.Contact.T7KeyIndexing
