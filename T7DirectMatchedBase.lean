module
public import T7DirectReplayBase
@[expose] public section
namespace SparseMonotiles.Contact.DirectReplay
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000

noncomputable def matchCheck (a b : Fin 1024) (q : Pose 7) : Bool :=
  decide (RootZeroPilot7.sourceKey a = q.boxKey geometry.denominator (RootZeroPilot7.sourceKey b))

noncomputable def directMatchCheck (a b : Fin 1024) (r : PackedRow) : Bool :=
  matchCheck a b (decodePose r.code) && rowCheck r

theorem classify_from_match {a b : Fin 1024} {r : PackedRow}
    (checked : directMatchCheck a b r = true)
    (asymmetric : (RootZeroPilot7.sourceKey b).Asymmetric)
    (p : Pose 7)
    (matched : RootZeroPilot7.sourceKey a =
      p.boxKey geometry.denominator (RootZeroPilot7.sourceKey b))
    (legal : geometry.LegalContact p) : p ∈ M7 := by
  have hc : matchCheck a b (decodePose r.code) = true ∧ rowCheck r = true := by
    simpa only [directMatchCheck, Bool.and_eq_true_iff] using checked
  have hq : RootZeroPilot7.sourceKey a =
      (decodePose r.code).boxKey geometry.denominator (RootZeroPilot7.sourceKey b) :=
    of_decide_eq_true hc.1
  have he : p = decodePose r.code :=
    Pose.boxKey_injective_of_asymmetric (by decide) asymmetric (matched.symm.trans hq)
  have good : Good (decodePose r.code) := certCheck_sound hc.2
  exact he.symm ▸ good (he ▸ legal)
#print axioms classify_from_match
end SparseMonotiles.Contact.DirectReplay
