module

public import SparseMonotiles.GeneratorKeyIndexing5Base

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem generatorIndexBindingChunk3 : ∀ j : Fin 32, generatorIndexBinding ⟨96 + j.val, by omega⟩ := by decide +kernel
#print axioms generatorIndexBindingChunk3
end SparseMonotiles.Contact.IndexedData5
