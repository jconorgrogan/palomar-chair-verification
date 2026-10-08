module
public import PilotBase
public import CatalogInverseClosure
@[expose] public section
namespace SparseMonotiles.Contact.PackedReplay
open IndexedData7 CarrierHierarchy ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def permLookup (i : Nat) : Equiv.Perm (Fin 7) :=
  (if i < 56 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then perm0 else (if i < 2 then perm1 else perm2)) else (if i < 5 then (if i < 4 then perm3 else perm4) else (if i < 6 then perm5 else perm6))) else (if i < 10 then (if i < 8 then perm7 else (if i < 9 then perm8 else perm9)) else (if i < 12 then (if i < 11 then perm10 else perm11) else (if i < 13 then perm12 else perm13)))) else (if i < 21 then (if i < 17 then (if i < 15 then perm14 else (if i < 16 then perm15 else perm16)) else (if i < 19 then (if i < 18 then perm17 else perm18) else (if i < 20 then perm19 else perm20))) else (if i < 24 then (if i < 22 then perm21 else (if i < 23 then perm22 else perm23)) else (if i < 26 then (if i < 25 then perm24 else perm25) else (if i < 27 then perm26 else perm27))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then perm28 else (if i < 30 then perm29 else perm30)) else (if i < 33 then (if i < 32 then perm31 else perm32) else (if i < 34 then perm33 else perm34))) else (if i < 38 then (if i < 36 then perm35 else (if i < 37 then perm36 else perm37)) else (if i < 40 then (if i < 39 then perm38 else perm39) else (if i < 41 then perm40 else perm41)))) else (if i < 49 then (if i < 45 then (if i < 43 then perm42 else (if i < 44 then perm43 else perm44)) else (if i < 47 then (if i < 46 then perm45 else perm46) else (if i < 48 then perm47 else perm48))) else (if i < 52 then (if i < 50 then perm49 else (if i < 51 then perm50 else perm51)) else (if i < 54 then (if i < 53 then perm52 else perm53) else (if i < 55 then perm54 else perm55)))))) else (if i < 84 then (if i < 70 then (if i < 63 then (if i < 59 then (if i < 57 then perm56 else (if i < 58 then perm57 else perm58)) else (if i < 61 then (if i < 60 then perm59 else perm60) else (if i < 62 then perm61 else perm62))) else (if i < 66 then (if i < 64 then perm63 else (if i < 65 then perm64 else perm65)) else (if i < 68 then (if i < 67 then perm66 else perm67) else (if i < 69 then perm68 else perm69)))) else (if i < 77 then (if i < 73 then (if i < 71 then perm70 else (if i < 72 then perm71 else perm72)) else (if i < 75 then (if i < 74 then perm73 else perm74) else (if i < 76 then perm75 else perm76))) else (if i < 80 then (if i < 78 then perm77 else (if i < 79 then perm78 else perm79)) else (if i < 82 then (if i < 81 then perm80 else perm81) else (if i < 83 then perm82 else perm83))))) else (if i < 98 then (if i < 91 then (if i < 87 then (if i < 85 then perm84 else (if i < 86 then perm85 else perm86)) else (if i < 89 then (if i < 88 then perm87 else perm88) else (if i < 90 then perm89 else perm90))) else (if i < 94 then (if i < 92 then perm91 else (if i < 93 then perm92 else perm93)) else (if i < 96 then (if i < 95 then perm94 else perm95) else (if i < 97 then perm96 else perm97)))) else (if i < 105 then (if i < 101 then (if i < 99 then perm98 else (if i < 100 then perm99 else perm100)) else (if i < 103 then (if i < 102 then perm101 else perm102) else (if i < 104 then perm103 else perm104))) else (if i < 108 then (if i < 106 then perm105 else (if i < 107 then perm106 else perm107)) else (if i < 110 then (if i < 109 then perm108 else perm109) else (if i < 111 then perm110 else perm111)))))))

def decodePose (code : Nat) : Pose 7 :=
  ⟨permLookup (code % 128),
   (fun i => decide ((code / 128 / (2 ^ i.val)) % 2 = 1)),
   (fun i => (((code / 16384 / (8 ^ i.val)) % 8 : Nat) : Int) - 2)⟩

inductive ForwardCert where
  | rejected (r : IndexedRejection 7 896)
  | catalog (i : Fin 408)

def catalogPose (i : Fin 408) : Pose 7 := Catalog7.supplied.get ⟨i.val, by change i.val < 408; exact i.isLt⟩

def Good (p : Pose 7) : Prop := geometry.LegalContact p → p ∈ M7

noncomputable def certCheck (p : Pose 7) : ForwardCert → Bool
  | .rejected r => decide (r.FastValid geometry p)
  | .catalog i => decide (p.SameCoordinates (catalogPose i))

theorem certCheck_sound {p : Pose 7} {c : ForwardCert}
    (h : certCheck p c = true) : Good p := by
  cases c with
  | rejected r =>
      have hv : r.FastValid geometry p := of_decide_eq_true h
      exact fun hp => (IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq hv) hp).elim
  | catalog i =>
      have he : p = catalogPose i := Pose.eq_of_sameCoordinates (of_decide_eq_true h)
      intro _
      rw [he]
      exact List.get_mem _ _

structure PackedRow where
  code : Nat
  cert : ForwardCert

noncomputable def rowCheck (r : PackedRow) : Bool := certCheck (decodePose r.code) r.cert

def CertifiedPose := {p : Pose 7 // Good p}

def inverseCertified (p : CertifiedPose) : CertifiedPose :=
  ⟨inversePose p.val, classify_M7_of_eq_inversePose rfl p.property⟩

noncomputable def certifiedRow {n : Nat} (rows : Fin n → PackedRow)
    (checked : allPairsB (fun (_ : Fin 1) (i : Fin n) => rowCheck (rows i)) = true)
    (i : Fin n) : CertifiedPose :=
  ⟨decodePose (rows i).code, certCheck_sound (allPairsB_sound checked 0 i)⟩

def originalPair (a b : Fin 1024) : Option (Pose 7) :=
  pairPose geometry.denominator (geometry.facet (RootZeroPilot7.sourceOwner a))
    (geometry.facet (RootZeroPilot7.sourceOwner b))
    (RootZeroPilot7.sourceKey a) (RootZeroPilot7.sourceKey b)

noncomputable def pairCheck (a b : Fin 1024) (p : Pose 7) : Bool :=
  pairFieldsMatchB geometry.denominator (geometry.facet (RootZeroPilot7.sourceOwner a))
    (geometry.facet (RootZeroPilot7.sourceOwner b))
    (RootZeroPilot7.sourceKey a) (RootZeroPilot7.sourceKey b) p

theorem classify_from_checked {a b : Fin 1024} (q : CertifiedPose)
    (checked : pairCheck a b q.val = true) (p : Pose 7)
    (generated : originalPair a b = some p) (legal : geometry.LegalContact p) : p ∈ M7 := by
  have eqn : originalPair a b = some q.val := pairFieldsMatchB_sound (by decide) checked
  have he : q.val = p := Option.some.inj (eqn.symm.trans generated)
  exact he ▸ q.property (he.symm ▸ legal)

noncomputable def directCheck (a b : Fin 1024) (r : PackedRow) : Bool :=
  pairCheck a b (decodePose r.code) && rowCheck r

theorem classify_from_direct {a b : Fin 1024} {r : PackedRow}
    (checked : directCheck a b r = true) (p : Pose 7)
    (generated : originalPair a b = some p) (legal : geometry.LegalContact p) : p ∈ M7 := by
  have hc : pairCheck a b (decodePose r.code) = true ∧ rowCheck r = true := by
    simpa only [directCheck, Bool.and_eq_true_iff] using checked
  exact classify_from_checked ⟨decodePose r.code, certCheck_sound hc.2⟩ hc.1 p generated legal

#print axioms certCheck_sound
#print axioms inverseCertified
#print axioms certifiedRow
#print axioms classify_from_checked
#print axioms classify_from_direct
end SparseMonotiles.Contact.PackedReplay
