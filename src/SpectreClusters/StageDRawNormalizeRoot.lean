module

public import SpectreClusters.StageDRawCaptureInterface
public import SpectreClusters.StageDRowTransport

@[expose] public section

namespace SpectreClusters.StageD.Raw

theorem root_owned_unnormalize (f : Cell → ClusterPlacement) (k : Turn) (t : Point)
    (q : ClusterPlacement)
    (h : ClusterRootOwned (moveClusterField (turnNeg k) (inverseTranslation k t) f) q) :
    ClusterRootOwned f (moveClusterPlacement k t q) := by
  intro c hc
  rw [clusterPlacementCells_moved] at hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have hm := moveClusterField_apply_moved (turnNeg k) (inverseTranslation k t)
    f (moveCell k t d)
  rw [moveCell_inverse] at hm
  have hx := congrArg (moveClusterPlacement k t) (hm.symm.trans (h d hd))
  simpa only [moveClusterPlacement_right_inverse] using hx

def NormalizedRawCaptures : Prop :=
  ∀ (f : Cell → ClusterPlacement), ValidClusterGridField f →
    ∀ kind, LegalClusterKind kind → ClusterRootOwned f (canonical kind) →
      ∃ i, i < (rawNeighborIDs kind).length ∧ ClusterPatchOwned f (rawPatch kind i)

theorem rawCaptures_of_normalized (h : NormalizedRawCaptures) : RawCaptures := by
  intro f hf root hr hk
  let g := moveClusterField (turnNeg root.turn) (inverseTranslation root.turn root.center) f
  have hg : ValidClusterGridField g := moveClusterField_valid _ _ f hf
  have he : moveClusterPlacement (turnNeg root.turn) (inverseTranslation root.turn root.center)
      root = canonical root.kind := by
    calc
      _ = moveClusterPlacement (turnNeg root.turn) (inverseTranslation root.turn root.center)
          (moveClusterPlacement root.turn root.center (canonical root.kind)) :=
        congrArg _ (moveClusterPlacement_canonical root).symm
      _ = _ := moveClusterPlacement_inverse _ _ _
  have hgr : ClusterRootOwned g (canonical root.kind) := by
    have ht := moveClusterField_rootOwned (turnNeg root.turn)
      (inverseTranslation root.turn root.center) f root hr
    simpa only [he] using ht
  obtain ⟨i,hi,hp⟩ := h g hg root.kind hk hgr
  refine ⟨i,hi,?_⟩
  intro p hp'
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
  exact root_owned_unnormalize f root.turn root.center q (hp q hq)
end SpectreClusters.StageD.Raw
