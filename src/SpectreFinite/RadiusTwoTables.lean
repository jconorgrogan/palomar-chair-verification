module

public import SpectreFinite.RadiusTwoTable0
public import SpectreFinite.RadiusTwoTable1
public import SpectreFinite.RadiusTwoTable2
public import SpectreFinite.RadiusTwoTable3
public import SpectreFinite.RadiusTwoTable4
public import SpectreFinite.RadiusTwoTable5
public import SpectreFinite.RadiusTwoTable6
public import SpectreFinite.RadiusTwoTable7
public import SpectreFinite.RadiusTwoTable8
public import SpectreFinite.RadiusTwoTable9
public import SpectreFinite.RadiusTwoTable10
public import SpectreFinite.RadiusTwoTable12
public import SpectreFinite.RadiusTwoTable13
public import SpectreFinite.RadiusTwoTable14
public import SpectreFinite.RadiusTwoTable15
public import SpectreFinite.RadiusTwoTable17

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusTwo
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem table0_member : table0 ∈ constraints := by
  rw [table0_eq]
  exact List.mem_map.mpr ⟨(-2,0), by decide, rfl⟩
theorem table1_member : table1 ∈ constraints := by
  rw [table1_eq]
  exact List.mem_map.mpr ⟨(-2,1), by decide, rfl⟩
theorem table2_member : table2 ∈ constraints := by
  rw [table2_eq]
  exact List.mem_map.mpr ⟨(-2,2), by decide, rfl⟩
theorem table3_member : table3 ∈ constraints := by
  rw [table3_eq]
  exact List.mem_map.mpr ⟨(-1,-1), by decide, rfl⟩
theorem table4_member : table4 ∈ constraints := by
  rw [table4_eq]
  exact List.mem_map.mpr ⟨(-1,0), by decide, rfl⟩
theorem table5_member : table5 ∈ constraints := by
  rw [table5_eq]
  exact List.mem_map.mpr ⟨(-1,1), by decide, rfl⟩
theorem table6_member : table6 ∈ constraints := by
  rw [table6_eq]
  exact List.mem_map.mpr ⟨(-1,2), by decide, rfl⟩
theorem table7_member : table7 ∈ constraints := by
  rw [table7_eq]
  exact List.mem_map.mpr ⟨(0,-2), by decide, rfl⟩
theorem table8_member : table8 ∈ constraints := by
  rw [table8_eq]
  exact List.mem_map.mpr ⟨(0,-1), by decide, rfl⟩
theorem table9_member : table9 ∈ constraints := by
  rw [table9_eq]
  exact List.mem_map.mpr ⟨(0,0), by decide, rfl⟩
theorem table10_member : table10 ∈ constraints := by
  rw [table10_eq]
  exact List.mem_map.mpr ⟨(0,1), by decide, rfl⟩
theorem table12_member : table12 ∈ constraints := by
  rw [table12_eq]
  exact List.mem_map.mpr ⟨(1,-2), by decide, rfl⟩
theorem table13_member : table13 ∈ constraints := by
  rw [table13_eq]
  exact List.mem_map.mpr ⟨(1,-1), by decide, rfl⟩
theorem table14_member : table14 ∈ constraints := by
  rw [table14_eq]
  exact List.mem_map.mpr ⟨(1,0), by decide, rfl⟩
theorem table15_member : table15 ∈ constraints := by
  rw [table15_eq]
  exact List.mem_map.mpr ⟨(1,1), by decide, rfl⟩
theorem table17_member : table17 ∈ constraints := by
  rw [table17_eq]
  exact List.mem_map.mpr ⟨(2,-1), by decide, rfl⟩
theorem covers_of_branches (D : Domains 19 State) (outs : List (List State))
    (v : Fin 19) (h : ∀ s ∈ D v, Covers (restrict D v s) constraints outs) :
    Covers D constraints outs := by
  intro f hf
  exact h (f v) (hf.1 v) f ⟨fits_restrict D f hf.1 v, hf.2⟩
end SpectreFinite.HexSearch.RadiusTwo
