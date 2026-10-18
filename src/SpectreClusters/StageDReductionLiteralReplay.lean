module

public import SpectreClusters.StageDReductionFastDecoder

@[expose] public section


/-! Replay a certificate against a separately bound six-ID row, avoiding repeated
normalization of the entire1766-row source list inside each reference check. -/
namespace SpectreClusters.StageD.Reduction

def literalRefCheckB (T : Tables) (k : ClusterKind) (ids : List Nat)
    (p : PackedCertificate) (m : Nat) : Bool :=
  if p.mask.testBit m then
    let idx := (p.refs / 2^(10*m)) % 1024
    let e := T.geometryAt idx
    idx < T.geometryCount && (e.kind == k) && (e.neighbor == p.neighbor) &&
      (e.target == m) && (e.source == 0 || ids.contains (e.source-1))
  else true

def literalCertificateCheckB (T : Tables) (s : Nat) (k : ClusterKind)
    (ids : List Nat) (p : PackedCertificate) : Bool :=
  ids.contains p.neighbor &&
    (List.range (compactCandidates (compactAt k p.neighbor).kind).length).all
      (literalRefCheckB T k ids p) &&
    (p.hit < T.hitCount) && ((T.hitAt p.hit).stage == s) &&
    ((T.hitAt p.hit).kind == (compactAt k p.neighbor).kind) &&
    ((T.hitAt p.hit).mask == p.mask)

theorem literalCertificateCheckB_binding (T : Tables) (s : Nat) (k : ClusterKind)
    (i : Nat) (p : PackedCertificate) :
    literalCertificateCheckB T s k (compactIDs k i) p =
      fastCertificateCheckB T s k i p := rfl

theorem stepCheckB_of_literal (s : Nat) (k : ClusterKind) (i : Nat)
    (ids : List Nat) (p : PackedCertificate)
    (hi : compactIDs k i = ids) (hp : packedCertificateAt s k i = p)
    (hc : literalCertificateCheckB tables s k ids p = true) :
    stepCheckB tables s k i = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  right
  rw [hp,← literalCertificateCheckB_binding,hi]
  exact hc

end SpectreClusters.StageD.Reduction
