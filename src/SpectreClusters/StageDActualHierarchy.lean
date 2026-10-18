module

public import SpectreClusters.StageDCheckedRecognition
public import SpectreFinite.NativeHierarchyAperiodicity

@[expose] public section


/-! The universal hierarchy on actual owned clusters. Aperiodicity of the
literal labelled field proves orbit injectivity; contact connectivity proves
surjectivity. No separate planar chart or topological covering is assumed. -/
namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch SpectreFinite.HexSearch.ParentOwnership

variable {X : Type}

theorem orbit_stabilizer_eq_zero (C : NativeHierarchy.ParentOccurrenceTheorem)
    (S : HexStepSystem X) (label : X → State) (root : X)
    (hl : GloballyLegal (S.labelField label root)) (v : Position)
    (hv : S.translate v root = root) : v = (0,0) :=
  NativeHierarchy.globallyLegal_period_zero C _ hl v
    (ClusterOrbit.lift_is_fieldPeriod S label (fun x => x)
      (fun _ _ => rfl) (fun _ => rfl) root v hv)

theorem orbit_injective_of_parent_occurrence (C : NativeHierarchy.ParentOccurrenceTheorem)
    (S : HexStepSystem X) (label : X → State) (root : X)
    (hl : GloballyLegal (S.labelField label root)) :
    Function.Injective (fun v => S.translate v root) := by
  intro u v huv
  have h := congrArg (S.translate (-v.1,-v.2)) huv
  rw [← S.translate_add,← S.translate_add] at h
  have he : addPos (-v.1,-v.2) v = (0,0) := by
    apply Prod.ext <;> simp only [addPos] <;> omega
  rw [he,S.translate_zero] at h
  have hz := orbit_stabilizer_eq_zero C S label root hl _ h
  have hx := congrArg Prod.fst hz
  have hy := congrArg Prod.snd hz
  apply Prod.ext <;> simp only [addPos] at hx hy ⊢ <;> omega

noncomputable def actualClusterChart (hD : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (base : Cell) :
    Position → ActualCluster f :=
  fun v => (actualHexSystem finalRowChecks hD hf).translate v (clusterCellOwner hf base)

theorem actualClusterChart_injective (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hD : FinalClusterCaptures) {f : Cell → ClusterPlacement}
    (hf : ValidClusterGridField f) (base : Cell) :
    Function.Injective (actualClusterChart hD hf base) :=
  orbit_injective_of_parent_occurrence C (actualHexSystem finalRowChecks hD hf)
    (clusterLabel hD hf) (clusterCellOwner hf base)
    (actualMarkedField_globallyLegal finalRowChecks hD hf _)

theorem actualClusterChart_surjective (hD : FinalClusterCaptures) (hh : HaloOrderBinding)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (base : Cell) :
    Function.Surjective (actualClusterChart hD hf base) := by
  intro p
  apply ClusterOrbit.owner_orbit_surjective (actualHexSystem finalRowChecks hD hf)
    (clusterCellOwner hf) (actual_contact_steps finalRowChecks hD hh hf) _ base p
  intro q
  obtain ⟨c,hc⟩ := cluster_owned_represented f q.val q.property
  exact ⟨c,Subtype.ext hc⟩

noncomputable def actualLegalField (hD : FinalClusterCaptures)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) (base : Cell) :
    NativeHierarchy.LegalField :=
  ⟨actualMarkedField finalRowChecks hD hf (clusterCellOwner hf base),
    actualMarkedField_globallyLegal finalRowChecks hD hf _⟩

noncomputable def actualHierarchyBlock (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hD : FinalClusterCaptures) {f : Cell → ClusterPlacement}
    (hf : ValidClusterGridField f) (base : Cell) (n : Nat) (x : Position) :
    List (ActualCluster f) :=
  (NativeHierarchy.blocks C n (actualLegalField hD hf base) x).map (actualClusterChart hD hf base)

theorem actualHierarchyBlock_nodup (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hD : FinalClusterCaptures) {f : Cell → ClusterPlacement}
    (hf : ValidClusterGridField f) (base : Cell) (n : Nat) (x : Position) :
    (actualHierarchyBlock C hD hf base n x).Nodup :=
  List.Pairwise.map (actualClusterChart hD hf base)
    (fun _ _ hne he => hne (actualClusterChart_injective C hD hf base he))
    (NativeHierarchy.blocks_nodup C n (actualLegalField hD hf base) x)

theorem actualHierarchyBlock_lower (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hD : FinalClusterCaptures) {f : Cell → ClusterPlacement}
    (hf : ValidClusterGridField f) (base : Cell) (n : Nat) (x : Position) :
    7^n ≤ (actualHierarchyBlock C hD hf base n x).length := by
  simpa only [actualHierarchyBlock,List.length_map] using
    (NativeHierarchy.blocks_lower C n (actualLegalField hD hf base) x)

theorem actualHierarchyBlock_cover (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hD : FinalClusterCaptures) (hh : HaloOrderBinding) {f : Cell → ClusterPlacement}
    (hf : ValidClusterGridField f) (base : Cell) (n : Nat) (p : ActualCluster f) :
    ∃ x, p ∈ actualHierarchyBlock C hD hf base n x := by
  obtain ⟨v,hv⟩ := actualClusterChart_surjective hD hh hf base p
  obtain ⟨x,hx⟩ := NativeHierarchy.blocks_cover C n (actualLegalField hD hf base) v
  exact ⟨x,List.mem_map.mpr ⟨v,hx,hv⟩⟩

theorem actualHierarchyBlock_disjoint (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hD : FinalClusterCaptures) {f : Cell → ClusterPlacement}
    (hf : ValidClusterGridField f) (base : Cell) (n : Nat) (x y : Position)
    (p : ActualCluster f) (hx : p ∈ actualHierarchyBlock C hD hf base n x)
    (hy : p ∈ actualHierarchyBlock C hD hf base n y) : x = y := by
  obtain ⟨u,hu,hup⟩ := List.mem_map.mp hx
  obtain ⟨v,hv,hvp⟩ := List.mem_map.mp hy
  have he := actualClusterChart_injective C hD hf base (hup.trans hvp.symm)
  subst v
  exact NativeHierarchy.blocks_disjoint C n (actualLegalField hD hf base) x y u hu hv

theorem sparse_grid_period_eq_zero (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hA : StageA.FinalCaptures) (hD : FinalClusterCaptures) (hh : HaloOrderBinding)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hs : StageA.SparseTurtles f)
    (u : Point) (hu : GridFieldTranslationPeriod f u) : u = (0,0) := by
  by_cases hzero : u = (0,0)
  · exact hzero
  · obtain ⟨F,hF,v,hv,hperiod⟩ := checked_sparse_ht_period_gives_marked_period hA hD hh f hf hs u hzero hu
    exact False.elim (hv (NativeHierarchy.globallyLegal_period_zero C F hF v hperiod))

end SpectreClusters.StageD
