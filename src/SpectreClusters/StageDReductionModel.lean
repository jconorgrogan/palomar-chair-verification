module

public import SpectreClusters.StageDReductionRows
public import SpectreClusters.StageDRowTransport

@[expose] public section


/-! Sound mask-compressed elimination of owned cluster patches. A marked
candidate has an explicit cell collision; every previous-round target row
must contain one marked candidate. No raw-row pair scan is trusted. -/
namespace SpectreClusters.StageD.Reduction

structure BlockGeometry where
  kind : ClusterKind
  neighbor : Nat
  source : Nat
  target : Nat
  cell : Cell

def sourcePose (k : ClusterKind) (a : Nat) : ClusterPlacement :=
  if a = 0 then canonical k else compactAt k (a-1)

def targetPose (k : ClusterKind) (n m : Nat) : ClusterPlacement :=
  let p := compactAt k n
  moveClusterPlacement p.turn p.center (compactAt p.kind m)

def geometryCheckB (e : BlockGeometry) : Bool :=
  clashB [sourcePose e.kind e.source] [targetPose e.kind e.neighbor e.target]
    (some ⟨0,0,e.cell⟩)

theorem geometryCheck_not_owned (f : Cell → ClusterPlacement) (e : BlockGeometry)
    (h : geometryCheckB e = true)
    (ha : ClusterRootOwned f (sourcePose e.kind e.source))
    (hb : ClusterRootOwned f (targetPose e.kind e.neighbor e.target)) : False := by
  apply clashB_not_owned f _ _ _ h
  · intro p hp
    simpa only [List.mem_singleton.mp hp] using ha
  · intro p hp
    simpa only [List.mem_singleton.mp hp] using hb

structure HitGroup where
  stage : Nat
  kind : ClusterKind
  mask : Nat

def hitCheckB (kept : Nat → ClusterKind → List Nat) (g : HitGroup) : Bool :=
  (kept g.stage g.kind).all fun i => (compactIDs g.kind i).any fun m =>
    decide (m < (compactCandidates g.kind).length) && g.mask.testBit m

structure RejectCertificate where
  neighbor : Nat
  mask : Nat
  refs : Array Nat
  hit : Nat

structure Tables where
  kept : Nat → ClusterKind → List Nat
  geometryCount : Nat
  geometryAt : Nat → BlockGeometry
  hitCount : Nat
  hitAt : Nat → HitGroup
  certificate : Nat → ClusterKind → Nat → RejectCertificate

def refCheckB (T : Tables) (k : ClusterKind) (i : Nat) (c : RejectCertificate) (m : Nat) : Bool :=
  if c.mask.testBit m then
    let idx := (c.refs[m]?).getD 0
    let e := T.geometryAt idx
    idx < T.geometryCount && (e.kind == k) && (e.neighbor == c.neighbor) &&
      (e.target == m) && (e.source == 0 || (compactIDs k i).contains (e.source-1))
  else true

def certificateCheckB (T : Tables) (s : Nat) (k : ClusterKind) (i : Nat)
    (c : RejectCertificate) : Bool :=
  (compactIDs k i).contains c.neighbor &&
    (List.range (compactCandidates (compactAt k c.neighbor).kind).length).all (refCheckB T k i c) &&
    (c.hit < T.hitCount) && ((T.hitAt c.hit).stage == s) &&
    ((T.hitAt c.hit).kind == (compactAt k c.neighbor).kind) &&
    ((T.hitAt c.hit).mask == c.mask)

def stepCheckB (T : Tables) (s : Nat) (k : ClusterKind) (i : Nat) : Bool :=
  (T.kept (s+1) k).contains i || certificateCheckB T s k i (T.certificate s k i)

/-- All geometry is checked once and may be reused by many rejected rows. -/
def GeometryValid (T : Tables) : Prop :=
  ∀ n, n < T.geometryCount → geometryCheckB (T.geometryAt n) = true

/-- All identical hit masks are checked once per preceding-round row family. -/
def HitsValid (T : Tables) : Prop :=
  ∀ n, n < T.hitCount → hitCheckB T.kept (T.hitAt n) = true

theorem certificate_not_owned (T : Tables) (hg : GeometryValid T) (hh : HitsValid T)
    (s : Nat) (hcap : Captures (T.kept s)) (k : ClusterKind) (i : Nat) (c : RejectCertificate)
    (hc : certificateCheckB T s k i c = true)
    (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f)
    (ha : ClusterPatchOwned f (compactPatch k i)) : False := by
  simp only [certificateCheckB,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,
    List.contains_iff_mem] at hc
  obtain ⟨⟨⟨⟨⟨hn,href⟩,hbound⟩,hstage⟩,hkind⟩,hmask⟩ := hc
  let p := compactAt k c.neighbor
  have hp : ClusterRootOwned f p := ha p (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_,hn,rfl⟩))
  obtain ⟨j,hj,howned⟩ := hcap f hf p hp (cluster_owned_kind f hf p hp)
  have hit := hh c.hit hbound
  simp only [hitCheckB,hstage,hkind,hmask] at hit
  have hitj := List.all_eq_true.mp hit j hj
  obtain ⟨m,hm,hmb⟩ := List.any_eq_true.mp hitj
  have hmb' : m < (compactCandidates p.kind).length ∧ c.mask.testBit m = true := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using hmb
  have hrf := List.all_eq_true.mp href m (List.mem_range.mpr hmb'.1)
  simp only [refCheckB,hmb'.2,if_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,
    Bool.or_eq_true,List.contains_iff_mem] at hrf
  obtain ⟨⟨⟨⟨hebound,hek⟩,hen⟩,hem⟩,hes⟩ := hrf
  let idx := (c.refs[m]?).getD 0
  let e := T.geometryAt idx
  have hs : sourcePose e.kind e.source ∈ compactPatch k i := by
    rw [hek]
    rcases hes with hz | hm
    · change e.source = 0 at hz
      simp [sourcePose,hz,compactPatch]
    · by_cases hz : e.source = 0
      · simp [sourcePose,hz,compactPatch]
      · unfold sourcePose
        rw [if_neg hz]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_,hm,rfl⟩)
  have ht : ClusterRootOwned f (targetPose e.kind e.neighbor e.target) := by
    rw [hek,hen,hem]
    apply howned
    apply List.mem_map.mpr
    exact ⟨compactAt p.kind m,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨m,hm,rfl⟩),rfl⟩
  exact geometryCheck_not_owned f e (hg idx hebound) (ha _ hs) ht

theorem compactPatch_owned_normalized (f : Cell → ClusterPlacement) (k : ClusterKind)
    (i : Nat) (p : ClusterPlacement) (h : ClusterPatchOwned f (compactMovedPatch k i p)) :
    ClusterPatchOwned (moveClusterField (turnNeg p.turn) (inverseTranslation p.turn p.center) f)
      (compactPatch k i) := by
  intro q hq
  have hq' := h (moveClusterPlacement p.turn p.center q) (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hm := moveClusterField_rootOwned (turnNeg p.turn) (inverseTranslation p.turn p.center) f _ hq'
  simpa only [moveClusterPlacement_inverse] using hm

theorem captures_next (T : Tables) (hg : GeometryValid T) (hh : HitsValid T)
    (s : Nat) (hcap : Captures (T.kept s))
    (hc : ∀ k, LegalClusterKind k → (T.kept s k).all (stepCheckB T s k) = true) :
    Captures (T.kept (s+1)) := by
  intro f hf p hp hk
  obtain ⟨i,hi,hoi⟩ := hcap f hf p hp hk
  have hcheck := List.all_eq_true.mp (hc p.kind hk) i hi
  simp only [stepCheckB,Bool.or_eq_true,List.contains_iff_mem] at hcheck
  rcases hcheck with hkeep | hreject
  · exact ⟨i,hkeep,hoi⟩
  · exact False.elim (certificate_not_owned T hg hh s hcap p.kind i _ hreject
      (moveClusterField (turnNeg p.turn) (inverseTranslation p.turn p.center) f)
      (moveClusterField_valid _ _ f hf) (compactPatch_owned_normalized f p.kind i p hoi))

end SpectreClusters.StageD.Reduction
