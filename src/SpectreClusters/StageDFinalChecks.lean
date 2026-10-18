module

public import SpectreClusters.StageDLocalCertificates
public import SpectreClusters.StageDFinalRowCheck0
public import SpectreClusters.StageDFinalRowCheck1
public import SpectreClusters.StageDFinalRowCheck2
public import SpectreClusters.StageDFinalRowCheck3
public import SpectreClusters.StageDFinalRowCheck4
public import SpectreClusters.StageDFinalRowCheck5
public import SpectreClusters.StageDFinalRowCheck6
public import SpectreClusters.StageDFinalRowCheck7
public import SpectreClusters.StageDFinalRowCheck8
public import SpectreClusters.StageDFinalRowCheck9
public import SpectreClusters.StageDFinalRowCheck10
public import SpectreClusters.StageDFinalRowCheck11
public import SpectreClusters.StageDFinalRowCheck12
public import SpectreClusters.StageDFinalRowCheck13
public import SpectreClusters.StageDFinalRowCheck14
public import SpectreClusters.StageDFinalRowCheck15
public import SpectreClusters.StageDFinalRowCheck16
public import SpectreClusters.StageDFinalRowCheck17
public import SpectreClusters.StageDFinalRowCheck18
public import SpectreClusters.StageDFinalRowCheck19

@[expose] public section


namespace SpectreClusters.StageD

private theorem all_rows (P : Row → Prop)
    (h0 : P 0)
    (h1 : P 1)
    (h2 : P 2)
    (h3 : P 3)
    (h4 : P 4)
    (h5 : P 5)
    (h6 : P 6)
    (h7 : P 7)
    (h8 : P 8)
    (h9 : P 9)
    (h10 : P 10)
    (h11 : P 11)
    (h12 : P 12)
    (h13 : P 13)
    (h14 : P 14)
    (h15 : P 15)
    (h16 : P 16)
    (h17 : P 17)
    (h18 : P 18)
    (h19 : P 19)
    : ∀ i, P i := by
  intro i
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 := by omega
  rcases hv with hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv | hv
  · have hn : (0 : Row).val = 0 := by decide
    have he : i = (0 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h0
  · have hn : (1 : Row).val = 1 := by decide
    have he : i = (1 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h1
  · have hn : (2 : Row).val = 2 := by decide
    have he : i = (2 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h2
  · have hn : (3 : Row).val = 3 := by decide
    have he : i = (3 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h3
  · have hn : (4 : Row).val = 4 := by decide
    have he : i = (4 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h4
  · have hn : (5 : Row).val = 5 := by decide
    have he : i = (5 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h5
  · have hn : (6 : Row).val = 6 := by decide
    have he : i = (6 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h6
  · have hn : (7 : Row).val = 7 := by decide
    have he : i = (7 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h7
  · have hn : (8 : Row).val = 8 := by decide
    have he : i = (8 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h8
  · have hn : (9 : Row).val = 9 := by decide
    have he : i = (9 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h9
  · have hn : (10 : Row).val = 10 := by decide
    have he : i = (10 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h10
  · have hn : (11 : Row).val = 11 := by decide
    have he : i = (11 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h11
  · have hn : (12 : Row).val = 12 := by decide
    have he : i = (12 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h12
  · have hn : (13 : Row).val = 13 := by decide
    have he : i = (13 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h13
  · have hn : (14 : Row).val = 14 := by decide
    have he : i = (14 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h14
  · have hn : (15 : Row).val = 15 := by decide
    have he : i = (15 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h15
  · have hn : (16 : Row).val = 16 := by decide
    have he : i = (16 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h16
  · have hn : (17 : Row).val = 17 := by decide
    have he : i = (17 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h17
  · have hn : (18 : Row).val = 18 := by decide
    have he : i = (18 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h18
  · have hn : (19 : Row).val = 19 := by decide
    have he : i = (19 : Row) := Fin.ext (hv.trans hn.symm)
    exact he.symm ▸ h19

theorem all_pairs_checked : ∀ i : Row, ∀ d : Fin 6, ∀ j : Row, pairCheckB i d j = true := by
  apply all_rows (fun i => ∀ d : Fin 6, ∀ j : Row, pairCheckB i d j = true)
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row0_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row1_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row2_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row3_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row4_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row5_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row6_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row7_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row8_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row9_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row10_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row11_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row12_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row13_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row14_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row15_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row16_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row17_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row18_pairs_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row19_pairs_checked

theorem all_unique_checked : ∀ i : Row, ∀ j : Row, uniqueCheckB i j = true := by
  apply all_rows (fun i => ∀ j : Row, uniqueCheckB i j = true)
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row0_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row1_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row2_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row3_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row4_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row5_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row6_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row7_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row8_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row9_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row10_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row11_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row12_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row13_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row14_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row15_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row16_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row17_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row18_unique_checked
  · simpa only [List.all_eq_true,List.mem_finRange,forall_const] using row19_unique_checked

theorem all_basics_checked : ∀ i : Row,  rowBasicsB i = true := by
  apply all_rows (fun i =>  rowBasicsB i = true)
  · exact row0_basics_checked
  · exact row1_basics_checked
  · exact row2_basics_checked
  · exact row3_basics_checked
  · exact row4_basics_checked
  · exact row5_basics_checked
  · exact row6_basics_checked
  · exact row7_basics_checked
  · exact row8_basics_checked
  · exact row9_basics_checked
  · exact row10_basics_checked
  · exact row11_basics_checked
  · exact row12_basics_checked
  · exact row13_basics_checked
  · exact row14_basics_checked
  · exact row15_basics_checked
  · exact row16_basics_checked
  · exact row17_basics_checked
  · exact row18_basics_checked
  · exact row19_basics_checked

theorem finalRowChecks : FinalRowChecks :=
  ⟨all_pairs_checked,all_unique_checked,all_basics_checked⟩

end SpectreClusters.StageD
