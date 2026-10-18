module

public import SpectreClusters.KiteContactData

@[expose] public section

namespace SpectreClusters
set_option maxRecDepth 100000 in
theorem localContacts5_eq_filter :
    localContacts 5 = (contactCandidates ⟨(0,0),5⟩).filter
      (fun b => cellContactB ⟨(0,0),5⟩ b) := rfl
end SpectreClusters
