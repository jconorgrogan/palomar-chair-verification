module

public import SpectreClusters.KiteContactData

@[expose] public section

namespace SpectreClusters
set_option maxRecDepth 100000 in
theorem localContacts0_eq_filter :
    localContacts 0 = (contactCandidates ⟨(0,0),0⟩).filter
      (fun b => cellContactB ⟨(0,0),0⟩ b) := rfl
end SpectreClusters
