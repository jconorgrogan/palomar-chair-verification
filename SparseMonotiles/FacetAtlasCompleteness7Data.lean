module

public import SparseMonotiles.FacetAtlasCompleteness
public import SparseMonotiles.ContactCertificateDataIndexed7Base

@[expose] public section
namespace SparseMonotiles.Contact.FacetAtlasCompleteness7
def lookup (f : Facet 7) : Fin 896 :=
  ⟨IndexedData7.tagLookup f.binaryTag % 896, Nat.mod_lt _ (by decide)⟩
end SparseMonotiles.Contact.FacetAtlasCompleteness7
