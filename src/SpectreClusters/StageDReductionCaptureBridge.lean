module

public import SpectreClusters.StageDReductionModel
public import SpectreClusters.StageDRawCaptureInterface

@[expose] public section


/-! Exact original-ID transport between raw probe replay and compact masks. -/
namespace SpectreClusters.StageD.Reduction

theorem raw_captures_compact (hraw : Raw.RawCaptures)
    (hlength : ∀ k, (Raw.rawNeighborIDs k).length = (compactRowIDs k).length)
    (hpatch : ∀ k i, i < (compactRowIDs k).length → compactPatch k i = Raw.rawPatch k i) :
    Captures (fun k => List.range (compactRowIDs k).length) := by
  intro f hf p hp hk
  obtain ⟨i,hi,hoi⟩ := hraw f hf p hp hk
  rw [hlength] at hi
  refine ⟨i,List.mem_range.mpr hi,?_⟩
  simpa only [compactMovedPatch,hpatch p.kind i hi,Raw.rawMovedPatch] using hoi

theorem owned_id_retained (T : Tables) (hg : GeometryValid T) (hh : HitsValid T)
    (s : Nat) (hcap : Captures (T.kept s))
    (hc : ∀ k, LegalClusterKind k → (T.kept s k).all (stepCheckB T s k) = true)
    (k : ClusterKind) (hk : LegalClusterKind k) (i : Nat) (hi : i ∈ T.kept s k)
    (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (hoi : ClusterPatchOwned f (compactPatch k i)) : i ∈ T.kept (s+1) k := by
  have hcheck := List.all_eq_true.mp (hc k hk) i hi
  simp only [stepCheckB,Bool.or_eq_true,List.contains_iff_mem] at hcheck
  rcases hcheck with hkeep | hreject
  · exact hkeep
  · exact False.elim (certificate_not_owned T hg hh s hcap k i _ hreject f hf hoi)

theorem captures_three (T : Tables) (hg : GeometryValid T) (hh : HitsValid T)
    (h0 : Captures (T.kept 0))
    (hcheck : ∀ s, s < 3 → ∀ k, LegalClusterKind k →
      (T.kept s k).all (stepCheckB T s k) = true) : Captures (T.kept 3) := by
  have h1 := captures_next T hg hh 0 h0 (hcheck 0 (by decide))
  have h2 := captures_next T hg hh 1 h1 (hcheck 1 (by decide))
  exact captures_next T hg hh 2 h2 (hcheck 2 (by decide))

end SpectreClusters.StageD.Reduction
