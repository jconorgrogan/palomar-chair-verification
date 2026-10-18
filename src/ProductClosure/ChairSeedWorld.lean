module

public import ProductClosure.ChairGraphBridge
public import ProductClosure.ProductWorldReindex
public import PrimeFacetClosure.GeneratedWorldProfiles
public import RegisteredPrime.WorldExistence
public import AtlasPeriods.Aperiodicity
public import PhysicalRegistration.UnmarkedPeriodTransfer

@[expose] public section

/-! Nonvacuous checked chair seeds in the generalized complete-cell interface.
Both seed existence and every legal world's zero-period theorem are derived. -/
namespace ProductClosure.ChairBridge
open Set RegisteredPrime RegisteredPrime.PrimeFacetClosure
noncomputable section

@[simp] theorem placedCells_iff_occupies {m : ℕ} (q : Pose (m+1)) (z : World.Lattice (m+1)) :
    z ∈ World.placedCells (cells m) q ↔ Occupies q z := by
  simp only [World.placedCells, Set.mem_image, Finset.mem_coe, mem_cells,
    World.poseCellIndex_eq_cell, Occupies]

/-- No quotient of the full frame and no change to the occupied cells. -/
def ofRegisteredWorld {m : ℕ} (W : RegisteredWorld (m+1)) :
    World.CompleteTiling (World.placedCells (cells m)) where
  tiles := W.tiles
  cover z := by
    obtain ⟨q,hq,hz⟩ := W.covers z
    exact ⟨q,hq,(placedCells_iff_occupies q z).mpr hz⟩
  disjoint q hq r hr hne := Set.disjoint_left.mpr (by
    intro z hz hz'
    exact hne (W.nonoverlap q r hq hr z
      ((placedCells_iff_occupies q z).mp hz) ((placedCells_iff_occupies r z).mp hz')).eq)
  nonempty q _ := World.placedCells_nonempty (cells_nonempty m) q

/-- The generalized cell world is exactly the historical chair world. -/
def toRegisteredWorld {m : ℕ} (W : World.CompleteTiling (World.placedCells (cells m))) :
    RegisteredWorld (m+1) where
  tiles := W.tiles
  covers z := by
    obtain ⟨q,hq,hz⟩ := W.cover z
    exact ⟨q,hq,(placedCells_iff_occupies q z).mp hz⟩
  nonoverlap q r hq hr z hz hz' := by
    have he : q = r := by
      by_contra hne
      exact Set.disjoint_left.mp (W.disjoint q hq r hr hne)
        ((placedCells_iff_occupies q z).mpr hz) ((placedCells_iff_occupies r z).mpr hz')
    subst r
    exact Pose.Same.refl _

/-- Actual generalized coefficients for the exact previously checked E. -/
def seedCoefficients {m : ℕ} (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3) :=
  NativeCompiler.compiledCoefficients (S := cells m)
    (PhysicalRegistration.NativeChair.GeneratedCompiler.nativeDimension_ge_two hmod)
    (PhysicalRegistration.NativeChair.GeneratedCompiler.generators hp hmod)
    (PhysicalRegistration.NativeChair.GeneratedCompiler.generators_proper hp hmod)

/-- The factor language tests all native sites at every actual adjacent pair. -/
def SeedProfileLanguage {m : ℕ} (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3)
    (q r : Pose (m+1)) : Prop :=
  NativeCompiler.FullProfileMating (seedCoefficients hp hmod)
    (PhysicalRegistration.NativeChair.poseIsometry (q.relative r))

/-- The original nested-supertiling theorem supplies a complete world satisfying
all generalized compiler equations, not just one selected equation per contact. -/
theorem seed_world_exists {m : ℕ} (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3) :
    ∃ W : World.CompleteTiling (World.placedCells (cells m)),
      ∀ q ∈ W.tiles, ∀ r ∈ W.tiles, q ≠ r → SeedProfileLanguage hp hmod q r := by
  obtain ⟨W,hW⟩ := registered_E_world_exists (minusParameters (m+1) hp hmod)
  refine ⟨ofRegisteredWorld W, ?_⟩
  intro q hq r hr hne
  apply (compiled_fullProfile_iff _ _ _ _).mpr
  exact PhysicalRegistration.NativeChair.generatedWorld_fullProfileMating hp hmod W hW hq hr hne

/-- Every adjacent-owner profile world is genuinely atlas-legal. The owner's
existence and uniqueness are inherited from actual complete cell coverage. -/
theorem seed_world_arithmetic_atlas {m : ℕ}
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3)
    (W : World.CompleteTiling (World.placedCells (cells m)))
    (hl : W.IsLegal World.LatticeAdjacent (SeedProfileLanguage hp hmod)) :
    ArithmeticAtlasLegal (minusParameters (m+1) hp hmod) (toRegisteredWorld W) := by
  intro q r hq hr hc
  obtain ⟨a,b,ha,hb,hab⟩ := hc.2
  have hoa : W.owner a = q := W.owner_eq_of_mem hq ((placedCells_iff_occupies q a).mpr ha)
  have hob : W.owner b = r := W.owner_eq_of_mem hr ((placedCells_iff_occupies r b).mpr hb)
  have hne : q ≠ r := by
    intro he
    exact hc.1 a ⟨ha, he ▸ ha⟩
  have hpq := hl a b ((World.latticeAdjacent_iff_registered a b).mpr hab)
    (by intro he; exact hne (hoa.symm.trans (he.trans hob)))
  rw [hoa,hob] at hpq
  have hprofile := (compiled_fullProfile_iff _ _ _ _).mp hpq
  have hcr := q.inv.face_contact q r hc
  rw [Pose.inv_comp] at hcr
  exact PhysicalRegistration.NativeChair.GeneratedCompiler.fullProfile_arithmetic_atlas
    hp hmod (q.relative r) hcr hprofile

/-- This seed property applies to every complete legal world, not merely the
constructed example. Thus product factors inherit actual zero periods. -/
theorem seed_world_period_zero {m : ℕ}
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3)
    (W : World.CompleteTiling (World.placedCells (cells m)))
    (hl : W.IsLegal World.LatticeAdjacent (SeedProfileLanguage hp hmod))
    (v : World.Lattice (m+1))
    (hv : ∀ q, q ∈ W.tiles ↔ AtlasPeriods.translate v q ∈ W.tiles) : v = 0 :=
  AtlasPeriods.arithmetic_atlas_translation_aperiodic (minusParameters (m+1) hp hmod)
    (toRegisteredWorld W) (seed_world_arithmetic_atlas hp hmod W hl) v hv

/-- The exact image-equality period convention used by product decoding. -/
theorem seed_world_statePeriod_zero {m : ℕ}
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3)
    (W : World.CompleteTiling (World.placedCells (cells m)))
    (hl : W.IsLegal World.LatticeAdjacent (SeedProfileLanguage hp hmod))
    (v : World.Lattice (m+1)) (hv : W.HasStatePeriod (AtlasPeriods.translate v)) : v = 0 := by
  apply seed_world_period_zero hp hmod W hl v
  intro q
  constructor
  · intro hq
    have hh := Set.mem_image_of_mem (AtlasPeriods.translate v) hq
    rwa [hv] at hh
  · intro hq
    rw [← hv] at hq
    obtain ⟨r,hr,he⟩ := hq
    have hh := congrArg (AtlasPeriods.translate (-v)) he
    simp only [PhysicalRegistration.NativeChair.registered_translate_neg_cancel] at hh
    exact hh ▸ hr

def primeThree : Uniform.IsPrime 3 :=
  ⟨by decide, fun d hd => (show Nat.Prime 3 by decide).eq_one_or_self_of_dvd d hd⟩

end
end ProductClosure.ChairBridge
