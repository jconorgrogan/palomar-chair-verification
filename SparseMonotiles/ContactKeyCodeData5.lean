module

public import SparseMonotiles.ContactKeyCodeCertificateTools
public import SparseMonotiles.ContactCertificateDataIndexed5Base

@[expose] public section

/-! Static coordinate functions. Dictionary SHA256: 2a45419c64537bf0158ac7e4b52e741ea9ca864e83529db1d2de85975fe9124a. -/
namespace SparseMonotiles.Contact
namespace IndexedData5

def coordinateCode : KeyCoordinateCode where
  denominator := 19200
  height := 80
  width n := if n = 1920 then 240 else if n = 3840 then 300 else if n = 5760 then 360 else if n = 7680 then 420 else 0
  offset n := if n = 1920 then 80 else if n = 3840 then 75 else if n = 5760 then 72 else if n = 7680 then 70 else 0

end IndexedData5
end SparseMonotiles.Contact
