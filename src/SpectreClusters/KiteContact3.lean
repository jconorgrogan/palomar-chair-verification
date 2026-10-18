module

public import SpectreClusters.KiteContactData

@[expose] public section

namespace SpectreClusters
set_option maxRecDepth 100000 in
theorem localContacts3_eq_filter :
    localContacts 3 = (contactCandidates ⟨(0,0),3⟩).filter
      (fun b => cellContactB ⟨(0,0),3⟩ b) := rfl
end SpectreClusters
