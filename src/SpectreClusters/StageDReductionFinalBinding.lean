module

public import SpectreClusters.StageDReductionKept
public import SpectreClusters.StageDCaptureInterface

@[expose] public section


namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000

def finalRow (k : ClusterKind) (i : Nat) : Row :=
  match k with
  | .t7h => if i = 139 then 0 else if i = 140 then 1 else 0
  | .t8h => if i = 727 then 2 else if i = 729 then 3 else if i = 753 then 4 else if i = 759 then 5 else if i = 1237 then 6 else if i = 1253 then 7 else if i = 1267 then 8 else if i = 1275 then 9 else if i = 1627 then 10 else if i = 1628 then 11 else if i = 1651 then 12 else if i = 1652 then 13 else if i = 1716 then 14 else if i = 1732 then 15 else if i = 1747 then 16 else if i = 1748 then 17 else if i = 1755 then 18 else if i = 1756 then 19 else 0
  | .t6h => 0

def finalBindingB (k : ClusterKind) (i : Nat) : Bool :=
  (rowKind (finalRow k i) == k) &&
    (rowPatch (finalRow k i)).all (fun p => (compactPatch k i).any (clusterPoseEqB p))

theorem final_bindings_checked : ∀ k, LegalClusterKind k →
    (kept 3 k).all (finalBindingB k) = true := by
  intro k hk
  rcases hk with rfl | rfl <;> rfl

theorem final_capture_of_compact (hcap : Captures (kept 3)) : FinalClusterCaptures := by
  intro f hf p hp hk
  obtain ⟨i,hi,hoi⟩ := hcap f hf p hp hk
  have hb := List.all_eq_true.mp (final_bindings_checked p.kind hk) i hi
  simp only [finalBindingB,Bool.and_eq_true,beq_iff_eq] at hb
  refine ⟨finalRow p.kind i,hb.1,?_⟩
  intro q hq
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
  have hm := List.all_eq_true.mp hb.2 r hr
  obtain ⟨v,hv,he⟩ := List.any_eq_true.mp hm
  have heq := (clusterPoseEqB_iff r v).mp he
  apply hoi
  exact List.mem_map.mpr ⟨v,hv,congrArg (moveClusterPlacement p.turn p.center) heq.symm⟩
end SpectreClusters.StageD.Reduction
