module
public import AtlasInclusion7
@[expose] public section

/-! Generic exact presentation transport. This module imports no compact physical
library and does not claim that its hypotheses have been instantiated there. -/
namespace ExactRegisteredTransport
open RegisteredPrime

structure Bridge (d : Nat) (α : Type) where
  toRP : α → Pose d
  fromRP : Pose d → α
  from_to : ∀ a, fromRP (toRP a) = a
  to_from : ∀ q, toRP (fromRP q) = q
  occupies : α → Cell d → Prop
  occupies_iff : ∀ a c, occupies a c ↔ Occupies (toRP a) c
  adjacent : Cell d → Cell d → Prop
  adjacent_iff : ∀ a b, adjacent a b ↔ Adjacent a b
  normalize : α → α → α
  normalize_toRP : ∀ a b, toRP (normalize a b) = (toRP a).relative (toRP b)
  translate : Cell d → α → α
  translate_toRP : ∀ v a, toRP (translate v a) = AtlasPeriods.translate v (toRP a)

namespace Bridge
variable {d : Nat} {α : Type} (B : Bridge d α)

def CellContact (a b : α) : Prop :=
  ∃ c e, B.occupies a c ∧ B.occupies b e ∧ B.adjacent c e

def DisjointCells (a b : α) : Prop :=
  ∀ c, ¬ (B.occupies a c ∧ B.occupies b c)

theorem toRP_injective {a b : α} (h : B.toRP a = B.toRP b) : a = b := by
  have he := congrArg B.fromRP h
  simpa only [B.from_to] using he

/-- Disjointness is explicitly retained; bare cell contact is insufficient. -/
theorem faceContact_iff (a b : α) :
    FaceContact (B.toRP a) (B.toRP b) ↔ B.DisjointCells a b ∧ B.CellContact a b := by
  constructor
  · rintro ⟨hd, c, e, ha, hb, he⟩
    refine ⟨?_, c, e, (B.occupies_iff a c).mpr ha,
      (B.occupies_iff b e).mpr hb, (B.adjacent_iff c e).mpr he⟩
    intro x hx
    exact hd x ⟨(B.occupies_iff a x).mp hx.1, (B.occupies_iff b x).mp hx.2⟩
  · rintro ⟨hd, c, e, ha, hb, he⟩
    refine ⟨?_, c, e, (B.occupies_iff a c).mp ha,
      (B.occupies_iff b e).mp hb, (B.adjacent_iff c e).mp he⟩
    intro x hx
    exact hd x ⟨(B.occupies_iff a x).mpr hx.1, (B.occupies_iff b x).mpr hx.2⟩

structure World where
  tiles : α → Prop
  covers : ∀ c, ∃ a, tiles a ∧ B.occupies a c
  nonoverlap : ∀ a b, tiles a → tiles b → ∀ c,
    B.occupies a c → B.occupies b c → a = b

namespace World
variable {B} (W : B.World)

def Legal (L : α → Prop) : Prop :=
  ∀ a b, W.tiles a → W.tiles b → a ≠ b → B.CellContact a b → L (B.normalize a b)

def IsPeriod (v : Cell d) : Prop :=
  ∀ a, W.tiles a ↔ W.tiles (B.translate v a)

/-- Within a full nonoverlapping world, distinct cell contacts are face contacts. -/
theorem faceContact_iff_distinct (a b : α) (ha : W.tiles a) (hb : W.tiles b) :
    FaceContact (B.toRP a) (B.toRP b) ↔ a ≠ b ∧ B.CellContact a b := by
  rw [B.faceContact_iff]
  constructor
  · rintro ⟨hd, hc⟩
    refine ⟨?_, hc⟩
    intro he
    obtain ⟨c, e, hca, _, _⟩ := hc
    exact hd c ⟨hca, he ▸ hca⟩
  · rintro ⟨hne, hc⟩
    refine ⟨?_, hc⟩
    intro c h
    exact hne (W.nonoverlap a b ha hb c h.1 h.2)

/-- The image world is constructed with actual coverage and nonoverlap. -/
def toRegistered : RegisteredWorld d where
  tiles q := W.tiles (B.fromRP q)
  covers c := by
    obtain ⟨a, ha, hc⟩ := W.covers c
    exact ⟨B.toRP a, by simpa only [B.from_to] using ha, (B.occupies_iff a c).mp hc⟩
  nonoverlap q r hq hr c hqc hrc := by
    have hqc' : B.occupies (B.fromRP q) c :=
      (B.occupies_iff _ c).mpr (by simpa only [B.to_from] using hqc)
    have hrc' : B.occupies (B.fromRP r) c :=
      (B.occupies_iff _ c).mpr (by simpa only [B.to_from] using hrc)
    have he := congrArg B.toRP (W.nonoverlap _ _ hq hr c hqc' hrc')
    have eqr : q = r := by simpa only [B.to_from] using he
    subst r
    exact Pose.Same.refl _

theorem toRegistered_mem (a : α) : W.toRegistered.tiles (B.toRP a) ↔ W.tiles a := by
  change W.tiles (B.fromRP (B.toRP a)) ↔ W.tiles a
  rw [B.from_to]

/-- Only atlas membership is transported, not the stronger generated-E language. -/
theorem toRegistered_atlas_legal {L : α → Prop} (P : Parameters) (hd : P.p = d)
    (atlas : ∀ a, L a → ArithmeticAtlasContact P (hd ▸ B.toRP a))
    (legal : W.Legal L) :
    ArithmeticAtlasLegal P (hd ▸ W.toRegistered) := by
  subst d
  intro q r hq hr hc
  have hc' : FaceContact (B.toRP (B.fromRP q)) (B.toRP (B.fromRP r)) := by
    simpa only [B.to_from] using hc
  have hpair := (W.faceContact_iff_distinct _ _ hq hr).mp hc'
  have hl := legal _ _ hq hr hpair.1 hpair.2
  have ha := atlas _ hl
  simpa only [B.normalize_toRP, B.to_from] using ha

/-- The exact same integer vector is used in both marked-period predicates. -/
theorem toRegistered_period_iff (v : Cell d) :
    AtlasPeriods.TranslationPeriod W.toRegistered v ↔ W.IsPeriod v := by
  have hfrom (q : Pose d) :
      B.fromRP (AtlasPeriods.translate v q) = B.translate v (B.fromRP q) := by
    have h := congrArg B.fromRP (B.translate_toRP v (B.fromRP q))
    simpa only [B.from_to, B.to_from] using h.symm
  constructor
  · intro h a
    have hp := h (B.toRP a)
    change W.tiles (B.fromRP (B.toRP a)) ↔
      W.tiles (B.fromRP (AtlasPeriods.translate v (B.toRP a))) at hp
    simpa only [B.from_to, hfrom] using hp
  · intro h q
    change W.tiles (B.fromRP q) ↔ W.tiles (B.fromRP (AtlasPeriods.translate v q))
    rw [hfrom]
    exact h (B.fromRP q)

end World
end Bridge
/-- Conditional only on the exact presentation bridge and original catalog binding.
This does not instantiate either premise for the compact physical library. -/
theorem seven_dimensional_catalog_period_zero {α : Type}
    (B : Bridge 7 α) (W : B.World) (L : α → Prop)
    (binding : ∀ a, L a → B.toRP a ∈ CompactT7Preparation.literalCatalog)
    (legal : W.Legal L) (v : Cell 7) (period : W.IsPeriod v) :
    v = (fun _ => 0) := by
  apply AtlasPeriods.arithmetic_atlas_translation_aperiodic CompactT7Preparation.P7
    W.toRegistered
  · exact W.toRegistered_atlas_legal CompactT7Preparation.P7 rfl
      (fun a ha => CompactT7Preparation.literalCatalog_arithmeticAtlas _ (binding a ha)) legal
  · exact (W.toRegistered_period_iff v).mpr period

#print axioms Bridge.faceContact_iff
#print axioms Bridge.World.toRegistered
#print axioms Bridge.World.toRegistered_atlas_legal
#print axioms Bridge.World.toRegistered_period_iff
#print axioms seven_dimensional_catalog_period_zero
end ExactRegisteredTransport
