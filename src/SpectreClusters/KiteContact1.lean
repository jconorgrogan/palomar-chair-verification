module

public import SpectreClusters.KiteContactData

@[expose] public section

namespace SpectreClusters
set_option maxRecDepth 100000 in
theorem localContacts1_eq_filter :
    localContacts 1 = (contactCandidates ⟨(0,0),1⟩).filter
      (fun b => cellContactB ⟨(0,0),1⟩ b) := rfl
end SpectreClusters
