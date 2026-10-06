module

public import SparseMonotiles.ContactKeyCodeCertificateTools
public import SparseMonotiles.ContactCertificateDataIndexed7Base

@[expose] public section

/-! Static coordinate functions. Dictionary SHA256: ed2df7584bee8b5605045dcf59047a23533d6113db0de86ebfb80ae939554a2f. -/
namespace SparseMonotiles.Contact
namespace IndexedData7

def coordinateCode : KeyCoordinateCode where
  denominator := 188160
  height := 560
  width n := if n = 13440 then 1680 else if n = 26880 then 1960 else if n = 40320 then 2240 else if n = 53760 then 2520 else if n = 67200 then 2800 else if n = 80640 then 3080 else 0
  offset n := if n = 13440 then 560 else if n = 26880 then 490 else if n = 40320 then 448 else if n = 53760 then 420 else if n = 67200 then 400 else if n = 80640 then 385 else 0

end IndexedData7
end SparseMonotiles.Contact
