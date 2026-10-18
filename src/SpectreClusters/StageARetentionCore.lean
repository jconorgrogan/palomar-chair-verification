module

public import SpectreClusters.StageAWindowModel

@[expose] public section

namespace SpectreClusters.StageA

def retentionCheckB (stage : Nat) (kind : HTKind) (i : Nat) : Bool :=
  (keptIds (stage+1) kind).contains i || rejectionCheckB stage kind i

theorem retention_of_kept (stage : Nat) (kind : HTKind) (i : Nat)
    (h : (keptIds (stage+1) kind).contains i = true) :
    retentionCheckB stage kind i = true := by
  simp only [retentionCheckB,h,Bool.true_or]

theorem retention_of_rejected (stage : Nat) (kind : HTKind) (i : Nat)
    (h : rejectionCheckB stage kind i = true) :
    retentionCheckB stage kind i = true := by
  simp only [retentionCheckB,h,Bool.or_true]

theorem rejection_of_retention (stage : Nat) (kind : HTKind)
    (h : (keptIds stage kind).all (retentionCheckB stage kind) = true)
    (i : Nat) (hi : i ∈ keptIds stage kind) (hout : i ∉ keptIds (stage+1) kind) :
    rejectionCheckB stage kind i = true := by
  have hc := List.all_eq_true.mp h i hi
  have hn : (keptIds (stage+1) kind).contains i = false := by
    simpa using hout
  simpa only [retentionCheckB,hn,Bool.false_or] using hc

end SpectreClusters.StageA
