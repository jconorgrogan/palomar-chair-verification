module

public import SpectreClusters.StageDReductionKernelUnpack

@[expose] public section


/-! Decode just the referenced ten-bit field, with equality to the original
array-valued checker proved before any concrete fast replay is used. -/
namespace SpectreClusters.StageD.Reduction

theorem structural_ref_get (p : PackedCertificate) (m : Nat) (hm : m < 41) :
    ((unpackStructural p).refs[m]?).getD 0 = (p.refs / 2^(10*m)) % 1024 := by
  simp [unpackStructural,List.getElem?_range hm]

def fastRefCheckB (T : Tables) (k : ClusterKind) (i : Nat) (p : PackedCertificate) (m : Nat) : Bool :=
  if p.mask.testBit m then
    let idx := (p.refs / 2^(10*m)) % 1024
    let e := T.geometryAt idx
    idx < T.geometryCount && (e.kind == k) && (e.neighbor == p.neighbor) &&
      (e.target == m) && (e.source == 0 || (compactIDs k i).contains (e.source-1))
  else true

theorem fastRefCheckB_eq (T : Tables) (k : ClusterKind) (i : Nat)
    (p : PackedCertificate) (m : Nat) (hm : m < 41) :
    fastRefCheckB T k i p m = refCheckB T k i (unpackStructural p) m := by
  unfold fastRefCheckB refCheckB
  rw [structural_ref_get p m hm]
  rfl

def fastCertificateCheckB (T : Tables) (s : Nat) (k : ClusterKind) (i : Nat)
    (p : PackedCertificate) : Bool :=
  (compactIDs k i).contains p.neighbor &&
    (List.range (compactCandidates (compactAt k p.neighbor).kind).length).all (fastRefCheckB T k i p) &&
    (p.hit < T.hitCount) && ((T.hitAt p.hit).stage == s) &&
    ((T.hitAt p.hit).kind == (compactAt k p.neighbor).kind) &&
    ((T.hitAt p.hit).mask == p.mask)

theorem compactCandidates_length_bound (k : ClusterKind) : (compactCandidates k).length ≤ 41 := by
  cases k <;> decide

theorem fastCertificateCheckB_eq (T : Tables) (s : Nat) (k : ClusterKind) (i : Nat)
    (p : PackedCertificate) :
    fastCertificateCheckB T s k i p = certificateCheckB T s k i (unpackStructural p) := by
  have he : (List.range (compactCandidates (compactAt k p.neighbor).kind).length).all (fastRefCheckB T k i p) =
      (List.range (compactCandidates (compactAt k p.neighbor).kind).length).all
        (refCheckB T k i (unpackStructural p)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor
    · intro h m hm
      have hb : m < 41 := Nat.lt_of_lt_of_le (List.mem_range.mp hm) (compactCandidates_length_bound _)
      rw [← fastRefCheckB_eq T k i p m hb]
      exact h m hm
    · intro h m hm
      have hb : m < 41 := Nat.lt_of_lt_of_le (List.mem_range.mp hm) (compactCandidates_length_bound _)
      rw [fastRefCheckB_eq T k i p m hb]
      exact h m hm
  unfold fastCertificateCheckB certificateCheckB
  rw [he]
  rfl

def packedCertificateAt (s : Nat) (k : ClusterKind) (i : Nat) : PackedCertificate :=
  packedAt (match s,k with
    | 0,.t7h => (initialCertificatet7h[i]?).getD 0
    | 0,.t8h => (initialCertificatet8h[i]?).getD 0
    | 1,.t7h => if i = 127 then 1875 else if i = 134 then 1876 else if i = 136 then 1877 else if i = 143 then 1878 else 0
    | 1,.t8h => if i = 1269 then 1879 else if i = 1277 then 1880 else if i = 1325 then 1881 else if i = 1331 then 1882 else if i = 1629 then 1883 else if i = 1653 then 1884 else if i = 1717 then 1885 else if i = 1733 then 1886 else if i = 1749 then 1887 else if i = 1757 then 1888 else 0
    | 2,.t8h => if i = 1289 then 1889 else 0
    | _,_ => 0)


def fastStepCheckB (s : Nat) (k : ClusterKind) (i : Nat) : Bool :=
  (kept (s+1) k).contains i || fastCertificateCheckB tables s k i (packedCertificateAt s k i)

theorem fastStepCheckB_eq (s : Nat) (k : ClusterKind) (i : Nat) :
    fastStepCheckB s k i = stepCheckB tables s k i := by
  have he : unpackStructural (packedCertificateAt s k i) = tables.certificate s k i := by
    change kernelCertificateAt s k i = certificateAt s k i
    rw [kernelCertificateAt_eq]
  unfold fastStepCheckB stepCheckB
  rw [fastCertificateCheckB_eq,he]
  rfl

theorem fastStepCheckB_eq_fun (s : Nat) (k : ClusterKind) :
    fastStepCheckB s k = stepCheckB tables s k :=
  funext (fastStepCheckB_eq s k)

end SpectreClusters.StageD.Reduction
