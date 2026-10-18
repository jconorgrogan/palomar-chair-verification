module

public import SpectreClusters.KiteContactData

@[expose] public section

namespace SpectreClusters
set_option maxRecDepth 100000 in
theorem localContacts2_eq_filter :
    localContacts 2 = (contactCandidates ⟨(0,0),2⟩).filter
      (fun b => cellContactB ⟨(0,0),2⟩ b) := rfl
end SpectreClusters
