module

public import SpectreClusters.KiteContactData

@[expose] public section

namespace SpectreClusters
set_option maxRecDepth 100000 in
theorem localContacts4_eq_filter :
    localContacts 4 = (contactCandidates ⟨(0,0),4⟩).filter
      (fun b => cellContactB ⟨(0,0),4⟩ b) := rfl
end SpectreClusters
