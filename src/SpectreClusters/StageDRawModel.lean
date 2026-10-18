module

public import SpectreClusters.ClusterGridModel
public import SpectreClusters.FastChecks
public import SpectreClusters.FiniteCoverWords

@[expose] public section


/-! Soundness of small positive certificates for complete cluster candidate
lists. Literal witnesses and exhaustive raw corona replay are separate. -/
namespace SpectreClusters.StageD.Raw

def fallback : ClusterPlacement := ⟨.t7h,0,(0,0)⟩

def poseEqB (a b : ClusterPlacement) : Bool :=
  a.kind == b.kind && a.turn.val == b.turn.val &&
    a.center.1 == b.center.1 && a.center.2 == b.center.2

theorem poseEqB_iff (a b : ClusterPlacement) : poseEqB a b = true ↔ a = b := by
  cases a with
  | mk ka ra ca =>
    cases b with
    | mk kb rb cb => simp [poseEqB,Prod.ext_iff,Fin.ext_iff,and_assoc]

inductive CandidateWitness where
  | listed (index : Nat)
  | overlap (cell : Cell)

def witnessCheck (root : List Cell) (candidates : List ClusterPlacement)
    (p : ClusterPlacement) : CandidateWitness → Bool
  | .listed i => i < candidates.length && poseEqB p (candidates.getD i fallback)
  | .overlap c => root.any (cellEqB c) && (clusterPlacementCells p).any (cellEqB c)

theorem witnessCheck_sound (root : List Cell) (candidates : List ClusterPlacement)
    (p : ClusterPlacement) (w : CandidateWitness)
    (h : witnessCheck root candidates p w = true)
    (hd : DisjointCells root (clusterPlacementCells p)) : p ∈ candidates := by
  cases w with
  | listed i =>
    simp only [witnessCheck,Bool.and_eq_true,decide_eq_true_eq,poseEqB_iff] at h
    obtain ⟨hi,he⟩ := h
    have hm : candidates.getD i fallback ∈ candidates := by
      simpa [List.getD_eq_getElem?_getD,hi] using (List.getElem_mem hi)
    simpa only [he] using hm
  | overlap c =>
    simp only [witnessCheck,Bool.and_eq_true,List.any_eq_true,cellEqB_iff] at h
    obtain ⟨⟨a,ha,hea⟩,b,hb,heb⟩ := h
    have hca : c ∈ root := by simpa only [hea] using ha
    have hcb : c ∈ clusterPlacementCells p := by simpa only [heb] using hb
    exact False.elim (hd c hca hcb)

def alignedAt (c : Cell) : List ClusterPlacement :=
  [ClusterKind.t7h,ClusterKind.t8h].flatMap fun kind =>
    (clusterCells kind).map fun b => alignClusterPlacement kind b c

theorem mem_alignedAt (p : ClusterPlacement) (c : Cell)
    (hk : LegalClusterKind p.kind) (hc : c ∈ clusterPlacementCells p) :
    p ∈ alignedAt c := by
  obtain ⟨b,hb,hbc⟩ := List.mem_map.mp hc
  apply List.mem_flatMap.mpr
  have hkind : p.kind ∈ [ClusterKind.t7h,ClusterKind.t8h] := by
    rcases hk with h | h <;> simp [h]
  refine ⟨p.kind,hkind,List.mem_map.mpr ⟨b,hb,?_⟩⟩
  rw [←hbc]
  exact alignClusterPlacement_moved p b

def alignedChecks (root : List Cell) (candidates : List ClusterPlacement)
    (c : Cell) (witnesses : List CandidateWitness) : Bool :=
  (List.range (alignedAt c).length).all fun i =>
    witnessCheck root candidates ((alignedAt c).getD i fallback)
      (witnesses.getD i (.listed 0))

theorem alignedChecks_complete (root : List Cell) (candidates : List ClusterPlacement)
    (c : Cell) (witnesses : List CandidateWitness)
    (h : alignedChecks root candidates c witnesses = true)
    (p : ClusterPlacement) (hp : p ∈ alignedAt c)
    (hd : DisjointCells root (clusterPlacementCells p)) : p ∈ candidates := by
  have hi := List.idxOf_lt_length_of_mem hp
  have hc := List.all_eq_true.mp h ((alignedAt c).idxOf p) (List.mem_range.mpr hi)
  have he : (alignedAt c).getD ((alignedAt c).idxOf p) fallback = p := by
    simp [List.getD_eq_getElem?_getD,hi]
  rw [he] at hc
  exact witnessCheck_sound root candidates p _ hc hd

def haloCheckAt (root order : List Cell) (a : Cell) : Bool :=
  (contacts a).all fun c => root.any (cellEqB c) || order.any (cellEqB c)

theorem halo_subset_of_checks (root order : List Cell)
    (h : ∀ a ∈ root, haloCheckAt root order a = true) :
    ∀ c ∈ halo root, c ∈ order := by
  intro c hc
  obtain ⟨hout,a,ha,hac⟩ := (mem_halo_iff root c).mp hc
  have ht := List.all_eq_true.mp (h a ha) c ((mem_contacts_iff a c).mpr hac)
  simp only [Bool.or_eq_true,List.any_eq_true,cellEqB_iff] at ht
  rcases ht with ⟨b,hb,he⟩ | ⟨b,hb,he⟩
  · exact False.elim (hout (by simpa only [he] using hb))
  · simpa only [he] using hb

theorem candidates_complete (root order : List Cell) (candidates : List ClusterPlacement)
    (witnesses : Cell → List CandidateWitness)
    (hhalo : ∀ c ∈ halo root, c ∈ order)
    (hchecks : ∀ c ∈ order, alignedChecks root candidates c (witnesses c) = true)
    (p : ClusterPlacement) (hk : LegalClusterKind p.kind)
    (hp : ShapeContact root (clusterPlacementCells p))
    (hd : DisjointCells root (clusterPlacementCells p)) : p ∈ candidates := by
  obtain ⟨a,ha,c,hcp,hac⟩ := hp
  have hchalo : c ∈ halo root := (mem_halo_iff root c).mpr
    ⟨fun hcr => hd c hcr hcp,a,ha,hac⟩
  exact alignedChecks_complete root candidates c (witnesses c)
    (hchecks c (hhalo c hchalo)) p (mem_alignedAt p c hk hcp) hd

end SpectreClusters.StageD.Raw
