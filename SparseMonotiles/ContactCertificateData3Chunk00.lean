module

public import SparseMonotiles.ContactCertificateData3Base

@[expose] public section

namespace SparseMonotiles.Contact.Calibration3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem chunk0_checked : validate geometry chunk0 = true := by decide
#print axioms chunk0_checked
end SparseMonotiles.Contact.Calibration3
