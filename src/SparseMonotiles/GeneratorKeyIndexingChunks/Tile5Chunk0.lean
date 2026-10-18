module

public import SparseMonotiles.GeneratorKeyIndexing5Base

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem generatorIndexBindingChunk0 : ∀ j : Fin 32, generatorIndexBinding ⟨0 + j.val, by omega⟩ := by decide +kernel
#print axioms generatorIndexBindingChunk0
end SparseMonotiles.Contact.IndexedData5
