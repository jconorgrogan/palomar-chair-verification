module

public import SpectreClusters.StageDReductionHitCheck0
public import SpectreClusters.StageDReductionHitCheck1
public import SpectreClusters.StageDReductionHitCheck2
public import SpectreClusters.StageDReductionHitCheck3
public import SpectreClusters.StageDReductionHitCheck4
public import SpectreClusters.StageDReductionHitCheck5
public import SpectreClusters.StageDReductionHitCheck6
public import SpectreClusters.StageDReductionHitCheck7
public import SpectreClusters.StageDReductionHitCheck8
public import SpectreClusters.StageDReductionHitCheck9
public import SpectreClusters.StageDReductionHitCheck10
public import SpectreClusters.StageDReductionHitCheck11
public import SpectreClusters.StageDReductionHitCheck12
public import SpectreClusters.StageDReductionHitCheck13
public import SpectreClusters.StageDReductionHitCheck14
public import SpectreClusters.StageDReductionHitCheck15
public import SpectreClusters.StageDReductionHitCheck16
public import SpectreClusters.StageDReductionHitCheck17
public import SpectreClusters.StageDReductionHitCheck18
public import SpectreClusters.StageDReductionHitCheck19
public import SpectreClusters.StageDReductionHitCheck20
public import SpectreClusters.StageDReductionHitCheck21
public import SpectreClusters.StageDReductionHitCheck22
public import SpectreClusters.StageDReductionData

@[expose] public section


namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000

theorem hit_all_checked : (List.range hitCount).all (fun n => hitCheckB kept (hitAt n)) = true := by
  change [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88].all (fun n => hitCheckB kept (hitAt n)) = true
  simp only [List.all_cons,List.all_nil,hit0_checked, hit1_checked, hit2_checked, hit3_checked, hit4_checked, hit5_checked, hit6_checked, hit7_checked, hit8_checked, hit9_checked, hit10_checked, hit11_checked, hit12_checked, hit13_checked, hit14_checked, hit15_checked, hit16_checked, hit17_checked, hit18_checked, hit19_checked, hit20_checked, hit21_checked, hit22_checked, hit23_checked, hit24_checked, hit25_checked, hit26_checked, hit27_checked, hit28_checked, hit29_checked, hit30_checked, hit31_checked, hit32_checked, hit33_checked, hit34_checked, hit35_checked, hit36_checked, hit37_checked, hit38_checked, hit39_checked, hit40_checked, hit41_checked, hit42_checked, hit43_checked, hit44_checked, hit45_checked, hit46_checked, hit47_checked, hit48_checked, hit49_checked, hit50_checked, hit51_checked, hit52_checked, hit53_checked, hit54_checked, hit55_checked, hit56_checked, hit57_checked, hit58_checked, hit59_checked, hit60_checked, hit61_checked, hit62_checked, hit63_checked, hit64_checked, hit65_checked, hit66_checked, hit67_checked, hit68_checked, hit69_checked, hit70_checked, hit71_checked, hit72_checked, hit73_checked, hit74_checked, hit75_checked, hit76_checked, hit77_checked, hit78_checked, hit79_checked, hit80_checked, hit81_checked, hit82_checked, hit83_checked, hit84_checked, hit85_checked, hit86_checked, hit87_checked, hit88_checked] <;> rfl

theorem tables_hits_valid : HitsValid tables := by
  intro n hn
  exact List.all_eq_true.mp hit_all_checked n (List.mem_range.mpr hn)
end SpectreClusters.StageD.Reduction
