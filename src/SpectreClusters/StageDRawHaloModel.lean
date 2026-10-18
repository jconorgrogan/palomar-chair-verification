module

public import SpectreClusters.StageDRawData
public import SpectreClusters.StageDHaloData

@[expose] public section

namespace SpectreClusters.StageD.Raw

def cellsSubsetB (a b : List Cell) : Bool :=
  a.all fun c => b.any (cellEqB c)

theorem cellsSubsetB_sound (a b : List Cell) (h : cellsSubsetB a b = true) :
    ∀ c ∈ a, c ∈ b := by
  intro c hc
  have hx := List.all_eq_true.mp h c hc
  obtain ⟨d,hd,he⟩ := List.any_eq_true.mp hx
  have heq := (cellEqB_iff c d).mp he
  simpa only [heq] using hd

theorem cells_eq_members (a b : List Cell)
    (h : cellsSubsetB a b && cellsSubsetB b a = true) :
    ∀ c, c ∈ a ↔ c ∈ b := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨hab,hba⟩ := h
  exact fun c => ⟨cellsSubsetB_sound a b hab c,cellsSubsetB_sound b a hba c⟩
end SpectreClusters.StageD.Raw
