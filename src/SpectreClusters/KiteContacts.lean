module

public import SpectreClusters.KiteContact0
public import SpectreClusters.KiteContact1
public import SpectreClusters.KiteContact2
public import SpectreClusters.KiteContact3
public import SpectreClusters.KiteContact4
public import SpectreClusters.KiteContact5

@[expose] public section

namespace SpectreClusters
set_option maxRecDepth 100000 in
theorem localContacts_eq_filter : ∀ k : Turn,
    localContacts k = (contactCandidates ⟨(0,0),k⟩).filter
      (fun b => cellContactB ⟨(0,0),k⟩ b) := by
  exact Fin.cases localContacts0_eq_filter (Fin.cases localContacts1_eq_filter
    (Fin.cases localContacts2_eq_filter (Fin.cases localContacts3_eq_filter
      (Fin.cases localContacts4_eq_filter (Fin.cases localContacts5_eq_filter
        (fun i => Fin.elim0 i))))))

theorem mem_localContacts_iff (k : Turn) (b : Cell) :
    b ∈ localContacts k ↔ CellContact ⟨(0,0),k⟩ b := by
  rw [localContacts_eq_filter]
  simp only [List.mem_filter, cellContactB_iff]
  exact ⟨And.right,fun h => ⟨cellContact_mem_candidates _ _ h,h⟩⟩

def relativeCell (a b : Cell) : Cell := ⟨sub b.center a.center,b.sector⟩
def contacts (a : Cell) : List Cell := (localContacts a.sector).map (translateCell a.center)

theorem contact_relative_iff (a b : Cell) :
    CellContact a b ↔ CellContact ⟨(0,0),a.sector⟩ (relativeCell a b) := by
  constructor
  · rintro ⟨v,ha,hb⟩
    obtain ⟨va,hva,ea⟩ := List.mem_map.mp ha
    obtain ⟨vb,hvb,eb⟩ := List.mem_map.mp hb
    refine ⟨va,?_,?_⟩
    · apply List.mem_map.mpr
      exact ⟨va,hva,by simp [add,lattice]⟩
    · apply List.mem_map.mpr
      refine ⟨vb,hvb,?_⟩
      have hx := congrArg Prod.fst (ea.trans eb.symm)
      have hy := congrArg Prod.snd (ea.trans eb.symm)
      apply Prod.ext <;> simp [relativeCell,add,sub,lattice] at * <;> omega
  · rintro ⟨v,ha,hb⟩
    obtain ⟨va,hva,ea⟩ := List.mem_map.mp ha
    obtain ⟨vb,hvb,eb⟩ := List.mem_map.mp hb
    refine ⟨add (lattice a.center) va,?_,?_⟩
    · exact List.mem_map.mpr ⟨va,hva,rfl⟩
    · apply List.mem_map.mpr
      refine ⟨vb,hvb,?_⟩
      have hx := congrArg Prod.fst (ea.trans eb.symm)
      have hy := congrArg Prod.snd (ea.trans eb.symm)
      apply Prod.ext <;> simp [relativeCell,add,sub,lattice] at * <;> omega

theorem translate_relative (a b : Cell) : translateCell a.center (relativeCell a b) = b := by
  cases b
  unfold translateCell relativeCell
  congr 1
  apply Prod.ext <;> simp [add,sub] <;> omega

theorem relative_translate (a b : Cell) : relativeCell a (translateCell a.center b) = b := by
  cases b
  unfold translateCell relativeCell
  congr 1
  apply Prod.ext <;> simp [add,sub] <;> omega

/-- Exact, arbitrary-center finite contact classification. -/
theorem mem_contacts_iff (a b : Cell) : b ∈ contacts a ↔ CellContact a b := by
  constructor
  · intro h
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp h
    apply (contact_relative_iff _ _).mpr
    rw [relative_translate]
    exact (mem_localContacts_iff _ _).mp hc
  · intro h
    apply List.mem_map.mpr
    exact ⟨relativeCell a b,(mem_localContacts_iff _ _).mpr
      ((contact_relative_iff _ _).mp h),translate_relative a b⟩

end SpectreClusters
