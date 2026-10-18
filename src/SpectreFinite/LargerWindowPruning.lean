module

public import SpectreFinite.SignaturePruning
public import SpectreFinite.RotatedWindows

@[expose] public section


/-! Sound signature certificates on arbitrary finite windows. The chosen
shared coordinates and key trees are untrusted finite data. Completeness
uses only actual field restrictions, so malformed extra rows cause no gap. -/
namespace SpectreFinite.HexSearch.LargerWindowPruning

open SignaturePruning (KeyTree accepts stateCode)

def encode : List State → Nat
  | [] => 0
  | s :: ss => stateCode s + 54 * encode ss

def rightSignature (samples : List Position) (p : Patch) : Nat :=
  encode (samples.map (patchState p))

def leftSignature (delta : Position) (samples : List Position) (p : Patch) : Nat :=
  encode (samples.map (fun x => patchState p (addPos delta x)))

theorem extract_signatures (domain samples : List Position) (delta : Position)
    (hshared : ∀ x ∈ samples, x ∈ domain ∧ addPos delta x ∈ domain)
    (f : Position → State) (center : Position) :
    leftSignature delta samples (extract f center domain) =
      rightSignature samples (extract f (addPos center delta) domain) := by
  apply congrArg encode
  apply List.map_congr_left
  intro x hx
  have hs := hshared x hx
  change patchState (restriction (shiftedField f center) domain) (addPos delta x) =
    patchState (restriction (shiftedField f (addPos center delta)) domain) x
  rw [patchState_restriction _ _ _ hs.2, patchState_restriction _ _ _ hs.1]
  simp only [shiftedField, addPos_assoc]

inductive Verdict (n : Nat) where
  | keep (patch : Patch)
  | reject (patch : Patch) (direction : Fin n)

def Verdict.patch : Verdict n → Patch
  | .keep p => p
  | .reject p _ => p

def Verdict.kept : Verdict n → Option Patch
  | .keep p => some p
  | .reject _ _ => none

def checkCoverage (samples : Fin n → List Position) (trees : Fin n → KeyTree)
    (v : Verdict n) : Bool :=
  (List.finRange n).all (fun d => accepts (trees d) (rightSignature (samples d) v.patch))

def checkVerdict (offsets : Fin n → Position) (samples : Fin n → List Position)
    (trees : Fin n → KeyTree) : Verdict n → Bool
  | .keep _ => true
  | .reject p d => !(accepts (trees d) (leftSignature (offsets d) (samples d) p))

def checkRows (offsets : Fin n → Position) (samples : Fin n → List Position)
    (trees : Fin n → KeyTree) (rows : List (Verdict n)) : Bool :=
  rows.all (fun v => checkCoverage samples trees v && checkVerdict offsets samples trees v)

/-- Every occurring row survives. Retained rows need no extension witness,
and trees need no independent ordering, exactness, or construction theorem. -/
theorem certified_round (domain : List Position) (offsets : Fin n → Position)
    (samples : Fin n → List Position)
    (hshared : ∀ d, ∀ x ∈ samples d, x ∈ domain ∧ addPos (offsets d) x ∈ domain)
    (trees : Fin n → KeyTree) (rows : List (Verdict n))
    (hcheck : checkRows offsets samples trees rows = true)
    (f : Position → State) (hf : OccurrenceComplete f domain (rows.map Verdict.patch)) :
    OccurrenceComplete f domain (rows.filterMap Verdict.kept) := by
  have hall := List.all_eq_true.mp hcheck
  have hcover : ∀ p ∈ rows.map Verdict.patch, ∀ d,
      accepts (trees d) (rightSignature (samples d) p) = true := by
    intro p hp d
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hp
    have hc := (Bool.and_eq_true_iff.mp (hall v hv)).1
    exact List.all_eq_true.mp hc d (by simp)
  intro center
  obtain ⟨v,hv,he⟩ := List.mem_map.mp (hf center)
  cases v with
  | keep p =>
      exact List.mem_filterMap.mpr ⟨.keep p,hv,congrArg some he⟩
  | reject p d =>
      have hreject : accepts (trees d) (leftSignature (offsets d) (samples d) p) = false := by
        have h := (Bool.and_eq_true_iff.mp (hall (.reject p d) hv)).2
        change (!accepts (trees d) (leftSignature (offsets d) (samples d) p)) = true at h
        cases hk : accepts (trees d) (leftSignature (offsets d) (samples d) p) with
        | false => rfl
        | true => rw [hk] at h; exact Bool.noConfusion h
      have ha := hcover _ (hf (addPos center (offsets d))) d
      have hs := extract_signatures domain (samples d) (offsets d) (hshared d) f center
      change p = extract f center domain at he
      rw [← he] at hs
      rw [← hs, hreject] at ha
      exact Bool.noConfusion ha

theorem checkRows_append (offsets : Fin n → Position) (samples : Fin n → List Position)
    (trees : Fin n → KeyTree) (a b : List (Verdict n))
    (ha : checkRows offsets samples trees a = true)
    (hb : checkRows offsets samples trees b = true) :
    checkRows offsets samples trees (a ++ b) = true := by
  change (a ++ b).all _ = true
  rw [List.all_append]
  change (checkRows offsets samples trees a && checkRows offsets samples trees b) = true
  rw [ha,hb]
  rfl

theorem checkRows_flatten (offsets : Fin n → Position) (samples : Fin n → List Position)
    (trees : Fin n → KeyTree) (chunks : List (List (Verdict n)))
    (h : chunks.all (fun rows => checkRows offsets samples trees rows) = true) :
    checkRows offsets samples trees chunks.flatten = true := by
  induction chunks with
  | nil => rfl
  | cons a as ih =>
      have ha := (Bool.and_eq_true_iff.mp h).1
      have has := (Bool.and_eq_true_iff.mp h).2
      exact checkRows_append offsets samples trees a as.flatten ha (ih has)

#print axioms extract_signatures
#print axioms certified_round
end SpectreFinite.HexSearch.LargerWindowPruning
