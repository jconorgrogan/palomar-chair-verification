module

public import SpectreClusters.GridCoverModel
public import SpectreClusters.GridReductionTransport

@[expose] public section


/-! Exact finite corona model for genuine T7H/T8H cluster partitions.
No topology, marked classification, or raw-list completeness is assumed. -/
namespace SpectreClusters

structure ClusterPlacement where
  kind : ClusterKind
  turn : Turn
  center : Point
  deriving DecidableEq, Repr

def clusterPlacementCells (p : ClusterPlacement) : List Cell :=
  (clusterCells p.kind).map (moveCell p.turn p.center)

def LegalClusterKind (k : ClusterKind) : Prop := k = .t7h ∨ k = .t8h
instance (k : ClusterKind) : Decidable (LegalClusterKind k) :=
  inferInstanceAs (Decidable (_ ∨ _))

def moveClusterPlacement (k : Turn) (t : Point) (p : ClusterPlacement) : ClusterPlacement :=
  ⟨p.kind,turnAdd k p.turn,add t (rotate k p.center)⟩

def alignClusterPlacement (kind : ClusterKind) (b c : Cell) : ClusterPlacement :=
  let k := turnDiff c.sector b.sector
  ⟨kind,k,sub c.center (rotate k b.center)⟩

theorem alignClusterPlacement_moved (p : ClusterPlacement) (b : Cell) :
    alignClusterPlacement p.kind b (moveCell p.turn p.center b) = p := by
  unfold alignClusterPlacement moveCell translateCell rotateCell
  simp only [turnDiff_add]
  cases p with
  | mk kind turn center =>
    congr 1
    apply Prod.ext <;> simp [sub,add]

def clusterNeighbors (root : List Cell) : List ClusterPlacement :=
  ((halo root).flatMap fun c =>
    [ClusterKind.t7h,ClusterKind.t8h].flatMap fun kind =>
      (clusterCells kind).map fun b => alignClusterPlacement kind b c).eraseDups.filter
        (fun p => decide (DisjointCells root (clusterPlacementCells p)))

/-- A disjoint neighboring cluster covers an actual halo cell, so its pose is
in a finite alignment list without an assumed coordinate search bound. -/
theorem clusterNeighbors_complete (root : List Cell) (p : ClusterPlacement)
    (hk : LegalClusterKind p.kind) (h : ShapeContact root (clusterPlacementCells p))
    (hd : DisjointCells root (clusterPlacementCells p)) : p ∈ clusterNeighbors root := by
  obtain ⟨a,ha,c,hc,hcontact⟩ := h
  have hout : c ∉ root := fun hcr => hd c hcr hc
  have hhalo : c ∈ halo root := (mem_halo_iff root c).mpr ⟨hout,a,ha,hcontact⟩
  obtain ⟨b,hb,hbc⟩ := List.mem_map.mp hc
  apply List.mem_filter.mpr
  refine ⟨List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨c,hhalo,?_⟩),by simp [hd]⟩
  apply List.mem_flatMap.mpr
  have hkind : p.kind ∈ [ClusterKind.t7h,ClusterKind.t8h] := by
    rcases hk with h | h <;> simp [h]
  refine ⟨p.kind,hkind,List.mem_map.mpr ⟨b,hb,?_⟩⟩
  rw [←hbc]
  exact alignClusterPlacement_moved p b

def ValidClusterGridField (f : Cell → ClusterPlacement) : Prop :=
  ∀ c, LegalClusterKind (f c).kind ∧ c ∈ clusterPlacementCells (f c) ∧
    ∀ d ∈ clusterPlacementCells (f c), f d = f c

def ClusterRootOwned (f : Cell → ClusterPlacement) (root : ClusterPlacement) : Prop :=
  ∀ c ∈ clusterPlacementCells root, f c = root

theorem clusterField_compatible (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (a b : Cell) : f a = f b ∨ DisjointCells (clusterPlacementCells (f a)) (clusterPlacementCells (f b)) := by
  by_cases he : f a = f b
  · exact Or.inl he
  · refine Or.inr ?_
    intro c ha hb
    exact he (((hf a).2.2 c ha).symm.trans ((hf b).2.2 c hb))

theorem clusterHalo_field_neighbor (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (root : ClusterPlacement) (hr : ClusterRootOwned f root) (c : Cell)
    (hc : c ∈ halo (clusterPlacementCells root)) : f c ∈ clusterNeighbors (clusterPlacementCells root) := by
  obtain ⟨hout,a,ha,hcontact⟩ := (mem_halo_iff _ _).mp hc
  apply clusterNeighbors_complete _ (f c) (hf c).1 ⟨a,ha,c,(hf c).2.1,hcontact⟩
  intro d hd hdf
  have he : f c = root := ((hf c).2.2 d hdf).symm.trans (hr d hd)
  exact hout (he ▸ (hf c).2.1)

def clusterCoronaChoices (root : ClusterPlacement) (c : Cell) : List ClusterPlacement :=
  (clusterNeighbors (clusterPlacementCells root)).filter fun p => (clusterPlacementCells p).contains c

def ClusterCoronaCompatible (a b : Cell × ClusterPlacement) : Prop :=
  a.2 = b.2 ∨ DisjointCells (clusterPlacementCells a.2) (clusterPlacementCells b.2)
instance : DecidableRel ClusterCoronaCompatible := fun a b =>
  inferInstanceAs (Decidable (_ ∨ _))

def clusterCoronaAssignments (root : ClusterPlacement) : List (List (Cell × ClusterPlacement)) :=
  SpectreFinite.Search.enumerate (clusterCoronaChoices root) ClusterCoronaCompatible
    (halo (clusterPlacementCells root))

/-- Actual cluster-field restriction is in the complete finite search. The
literal 1910-row binding and marked classification are separate theorems. -/
theorem clusterGridRestriction_mem_coronaAssignments
    (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (root : ClusterPlacement) (hr : ClusterRootOwned f root) :
    ((halo (clusterPlacementCells root)).map fun c => (c,f c)) ∈ clusterCoronaAssignments root := by
  apply (SpectreFinite.Search.mem_enumerate_iff _ _ _ _).mpr
  refine ⟨?_,?_,?_⟩
  · simp [List.map_map,Function.comp_def]
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [List.getElem_map]
    exact clusterField_compatible f hf _ _
  · intro p hp
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
    apply List.mem_filter.mpr
    exact ⟨clusterHalo_field_neighbor f hf root hr c hc,by simpa using (hf c).2.1⟩

end SpectreClusters
