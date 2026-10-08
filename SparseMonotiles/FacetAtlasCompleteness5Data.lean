module

public import SparseMonotiles.FacetAtlasCompleteness
public import SparseMonotiles.ContactCertificateDataIndexed5Base

@[expose] public section
namespace SparseMonotiles.Contact.FacetAtlasCompleteness5
def lookup (f : Facet 5) : Fin 160 :=
  ⟨IndexedData5.tagLookup f.binaryTag % 160, Nat.mod_lt _ (by decide)⟩
end SparseMonotiles.Contact.FacetAtlasCompleteness5
