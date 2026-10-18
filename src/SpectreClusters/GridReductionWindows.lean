module

public import SpectreClusters.GridReductionTransport
public import SpectreClusters.FastChecks

@[expose] public section


/-! Sound finite rejection by overlapping owner windows. A window certificate
need only list sound cell alignments; it need not list all intersections.
The preservation theorem is universal over genuine fields, so normalizing
a neighbor gives the next support without any normalization-composition
assumption. Literal tables and their finite checks are separate inputs. -/
namespace SpectreClusters.GridReductionWindows

abbrev Word := List Nat
abbrev Rows := HTKind → Nat → Word
abbrev Kept := HTKind → List Nat
abbrev Encoder := (Cell → HTPlacement) → HTKind → Word

/-- Data only: all geometric and ownership assertions appear in propositions
below and must be proved by the caller's literal-table binding. -/
structure WindowData where
  domain : HTKind → List Cell
  ownerAt : HTKind → Word → Nat → HTPlacement
  candidate : HTKind → Nat → HTPlacement
  neighborIds : HTKind → Word → List Nat
  alignmentPairs : HTKind → Nat → List (Nat × Nat)

def Encodes (D : WindowData) (f : Cell → HTPlacement) (kind : HTKind) (word : Word) : Prop :=
  ∀ i (hi : i < (D.domain kind).length), D.ownerAt kind word i = f ((D.domain kind)[i]'hi)

/-- Bounds and the exact direct-motion cell equation are both certified.
Omitting intersections is safe: it merely weakens the rejection test. -/
def AlignmentSound (D : WindowData) (kind : HTKind) (neighborId : Nat) : Prop :=
  let p := D.candidate kind neighborId
  ∀ ij ∈ D.alignmentPairs kind neighborId,
    ∃ hi : ij.1 < (D.domain kind).length,
    ∃ hj : ij.2 < (D.domain p.kind).length,
      (D.domain kind)[ij.1]'hi = moveCell p.turn p.center ((D.domain p.kind)[ij.2]'hj)

def supportB (D : WindowData) (kind : HTKind) (word : Word)
    (neighborId : Nat) (support : Word) : Bool :=
  let p := D.candidate kind neighborId
  (D.alignmentPairs kind neighborId).all (fun ij =>
    poseEqB (D.ownerAt kind word ij.1)
      (movePlacement p.turn p.center (D.ownerAt p.kind support ij.2)))

/-- Encodings of the same genuine field agree at every certified overlap
cell. This lemma itself needs only exact encoding equalities. -/
theorem supportB_of_encodes (D : WindowData) (f : Cell → HTPlacement)
    (kind : HTKind) (word : Word) (neighborId : Nat) (support : Word)
    (hw : Encodes D f kind word)
    (hs : Encodes D (normalizeField f (D.candidate kind neighborId))
      (D.candidate kind neighborId).kind support)
    (halign : AlignmentSound D kind neighborId) :
    supportB D kind word neighborId support = true := by
  apply List.all_eq_true.mpr
  intro ij hij
  apply (poseEqB_iff _ _).mpr
  obtain ⟨hi,hj,hcell⟩ := halign ij hij
  rw [hw ij.1 hi,hs ij.2 hj]
  exact (congrArg f hcell).trans
    (denormalizeField_apply f (D.candidate kind neighborId)
      ((D.domain (D.candidate kind neighborId).kind)[ij.2]'hj)).symm

/-- Local correctness of the encoding, with no list-completeness premise. -/
def EncodingSound (D : WindowData) (encode : Encoder) : Prop :=
  ∀ f, ValidGridField f → ∀ kind, RootOwned f (originRoot kind) →
    Encodes D f kind (encode f kind) ∧
      ∀ n ∈ D.neighborIds kind (encode f kind), RootOwned f (D.candidate kind n)

/-- The universal previous-stage invariant. At stage zero it must be
proved from the complete finite enumeration, never introduced as an axiom. -/
def Captures (rows : Rows) (kept : Kept) (encode : Encoder) : Prop :=
  ∀ f, ValidGridField f → ∀ kind, RootOwned f (originRoot kind) →
    ∃ i ∈ kept kind, rows kind i = encode f kind

/-- Every removed row has one represented neighbor with no surviving
support. Original row IDs are retained unchanged between stages. -/
def RejectionCertificate (D : WindowData) (rows : Rows) (before after : Kept) : Prop :=
  ∀ kind, ∀ i ∈ before kind, i ∉ after kind →
    ∃ n ∈ D.neighborIds kind (rows kind i),
      AlignmentSound D kind n ∧
        ∀ j ∈ before (D.candidate kind n).kind,
          supportB D kind (rows kind i) n (rows (D.candidate kind n).kind j) = false

/-- Each actual row ID survives a sound rejection pass. There is no appeal
to extendability heuristics, disk topology, or a full overlap-pair table. -/
theorem actual_id_survives (D : WindowData) (rows : Rows) (encode : Encoder)
    (before after : Kept) (hencode : EncodingSound D encode)
    (hbefore : Captures rows before encode)
    (hreject : RejectionCertificate D rows before after)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (kind : HTKind)
    (hr : RootOwned f (originRoot kind)) (i : Nat)
    (hi : i ∈ before kind) (hword : rows kind i = encode f kind) :
    i ∈ after kind := by
  by_cases hin : i ∈ after kind
  · exact hin
  · obtain ⟨n,hn,halign,hnone⟩ := hreject kind i hi hin
    have hp : RootOwned f (D.candidate kind n) :=
      (hencode f hf kind hr).2 n (hword ▸ hn)
    have hvalid := normalizeField_valid f hf (D.candidate kind n)
    have hroot := normalizeField_rootOwned f (D.candidate kind n) hp
    obtain ⟨j,hj,hjword⟩ := hbefore (normalizeField f (D.candidate kind n))
      hvalid (D.candidate kind n).kind hroot
    have hw : Encodes D f kind (rows kind i) := hword ▸ (hencode f hf kind hr).1
    have hs : Encodes D (normalizeField f (D.candidate kind n))
        (D.candidate kind n).kind (rows (D.candidate kind n).kind j) :=
      hjword ▸ (hencode (normalizeField f (D.candidate kind n))
        hvalid (D.candidate kind n).kind hroot).1
    have hyes := supportB_of_encodes D f kind (rows kind i) n
      (rows (D.candidate kind n).kind j) hw hs halign
    have hno := hnone j hj
    rw [hyes] at hno
    cases hno

/-- Universal preservation is composable for any finite sequence of
kernel-checked rejection stages. Normalized neighbor fields are genuine
fields again, which is why the universal invariant suffices. -/
theorem captures_of_rejections (D : WindowData) (rows : Rows) (encode : Encoder)
    (before after : Kept) (hencode : EncodingSound D encode)
    (hbefore : Captures rows before encode)
    (hreject : RejectionCertificate D rows before after) :
    Captures rows after encode := by
  intro f hf kind hr
  obtain ⟨i,hi,hword⟩ := hbefore f hf kind hr
  exact ⟨i,actual_id_survives D rows encode before after hencode hbefore hreject
    f hf kind hr i hi hword,hword⟩

theorem captures_all_stages (D : WindowData) (rows : Rows) (encode : Encoder)
    (stages : Nat → Kept) (hencode : EncodingSound D encode)
    (hzero : Captures rows (stages 0) encode)
    (hstep : ∀ n, RejectionCertificate D rows (stages n) (stages (n+1))) :
    ∀ n, Captures rows (stages n) encode := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    exact captures_of_rejections D rows encode (stages n)
      (stages (n+1)) hencode ih (hstep n)

end SpectreClusters.GridReductionWindows
