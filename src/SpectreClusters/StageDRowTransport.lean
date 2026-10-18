module

public import SpectreClusters.StageDCaptureInterface
public import SpectreClusters.ClusterGridTranslations

@[expose] public section


/-! Source-correct covariance and uniqueness of actual final-row occurrences.
Finite completeness remains the explicit FinalClusterCaptures obligation. -/
namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch

theorem cluster_origin_mem (k : ClusterKind) :
    (⟨(0,0),0⟩ : Cell) ∈ clusterCells k := by cases k <;> decide

theorem cluster_owned_represented (f : Cell → ClusterPlacement) (p : ClusterPlacement)
    (hp : ClusterRootOwned f p) : ∃ c, f c = p := by
  let c : Cell := moveCell p.turn p.center ⟨(0,0),0⟩
  exact ⟨c,hp c (List.mem_map.mpr ⟨_,cluster_origin_mem p.kind,rfl⟩)⟩

theorem cluster_owned_kind (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (p : ClusterPlacement) (hp : ClusterRootOwned f p) : LegalClusterKind p.kind := by
  obtain ⟨c,rfl⟩ := cluster_owned_represented f p hp
  exact (hf c).1

theorem moveClusterPlacement_canonical (p : ClusterPlacement) :
    moveClusterPlacement p.turn p.center (canonical p.kind) = p := by
  have hz : turnAdd p.turn 0 = p.turn := by
    have h : ∀ k : Turn, turnAdd k 0 = k := by decide
    exact h p.turn
  cases p
  simp [moveClusterPlacement,canonical,rotate_zero_point,hz,add]

theorem movedPatch_compose (i : Row) (k : Turn) (t : Point) (p : ClusterPlacement) :
    (movedPatch i p).map (moveClusterPlacement k t) =
      movedPatch i (moveClusterPlacement k t p) := by
  simp only [movedPatch,List.map_map]
  apply List.map_congr_left
  intro q hq
  exact moveClusterPlacement_compose k p.turn t p.center q

theorem clusterPatchOwned_moved (f : Cell → ClusterPlacement)
    (A : List ClusterPlacement) (h : ClusterPatchOwned f A) (k : Turn) (t : Point) :
    ClusterPatchOwned (moveClusterField k t f) (A.map (moveClusterPlacement k t)) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact moveClusterField_rootOwned k t f q (h q hq)

theorem movedPatch_owned_normalized (f : Cell → ClusterPlacement) (i : Row)
    (p : ClusterPlacement) (h : ClusterPatchOwned f (movedPatch i p)) :
    ClusterPatchOwned (moveClusterField (turnNeg p.turn) (inverseTranslation p.turn p.center) f)
      (rowPatch i) := by
  intro q hq
  have hq' := h (moveClusterPlacement p.turn p.center q) (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hm := moveClusterField_rootOwned (turnNeg p.turn) (inverseTranslation p.turn p.center) f _ hq'
  simpa only [moveClusterPlacement_inverse] using hm

theorem movedPatch_owned_moved (f : Cell → ClusterPlacement) (i : Row)
    (p : ClusterPlacement) (h : ClusterPatchOwned f (movedPatch i p)) (k : Turn) (t : Point) :
    ClusterPatchOwned (moveClusterField k t f) (movedPatch i (moveClusterPlacement k t p)) := by
  rw [←movedPatch_compose]
  exact clusterPatchOwned_moved f _ h k t

theorem movedPatch_owned_period (f : Cell → ClusterPlacement) (u : Point)
    (hu : ClusterGridFieldTranslationPeriod f u) (i : Row)
    (p : ClusterPlacement) (h : ClusterPatchOwned f (movedPatch i p)) :
    ClusterPatchOwned f (movedPatch i (moveClusterPlacement 0 u p)) := by
  rw [←movedPatch_compose]
  intro q hq
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
  exact ClusterGridFieldTranslationPeriod.rootOwned f u hu r (h r hr)

theorem actual_row_unique (hunique : ∀ i j : Row, uniqueCheckB i j = true)
    (f : Cell → ClusterPlacement) (p : ClusterPlacement) (i j : Row)
    (hi : rowKind i = p.kind) (hj : rowKind j = p.kind)
    (hpi : ClusterPatchOwned f (movedPatch i p))
    (hpj : ClusterPatchOwned f (movedPatch j p)) : i = j := by
  exact row_eq_of_checked i j (hunique i j) (hi.trans hj.symm)
    (moveClusterField (turnNeg p.turn) (inverseTranslation p.turn p.center) f)
    (movedPatch_owned_normalized f i p hpi) (movedPatch_owned_normalized f j p hpj)

end SpectreClusters.StageD
