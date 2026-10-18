module

public import ClarkSeed.HierarchyAdapter
public import SparseMonotiles.CarrierHierarchyPeriods

@[expose] public section

/-! Transport of literal full-pose translation periods. This never replaces
state equality by equality of occupied footprints or by a frame quotient. -/
namespace ClarkSeed.PoseAdapter
noncomputable section
open SparseMonotiles

@[simp] theorem toRegistered_translatePose {d : ℕ} (v : Contact.Cell d)
    (p : Contact.Pose d) :
    toRegistered (CarrierHierarchy.translatePose v p) =
      RegisteredPrime.AtlasPeriods.translate v (toRegistered p) :=
  translate_toRegistered_formula v p

@[simp] theorem toContact_translate {d : ℕ} (v : Contact.Cell d)
    (p : RegisteredPrime.Pose d) :
    toContact (RegisteredPrime.AtlasPeriods.translate v p) =
      CarrierHierarchy.translatePose v (toContact p) := by
  apply toRegistered_injective
  simp

/-- Translation is injective on the entire current registered state. -/
theorem registered_translate_injective {d : ℕ} (v : Contact.Cell d) :
    Function.Injective (RegisteredPrime.AtlasPeriods.translate v) := by
  intro p q h
  apply RegisteredPrime.Pose.Same.eq
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa only [RegisteredPrime.AtlasPeriods.translate] using
      congrArg (fun r : RegisteredPrime.Pose d => r.frame.perm i) h
  · intro i
    simpa only [RegisteredPrime.AtlasPeriods.translate] using
      congrArg (fun r : RegisteredPrime.Pose d => r.frame.negative i) h
  · intro i
    exact add_left_cancel (congrArg (fun r : RegisteredPrime.Pose d => r.anchor i) h)

theorem registered_translate_cancel {d : ℕ} (v : Contact.Cell d)
    (p : RegisteredPrime.Pose d) :
    RegisteredPrime.AtlasPeriods.translate v
      (RegisteredPrime.AtlasPeriods.translate (-v) p) = p := by
  apply RegisteredPrime.Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  change v i + (-v i + p.anchor i) = p.anchor i
  omega

/-- Equality of the translated full-state set is equivalent to membership
invariance, because the exact translation map is bijective. -/
theorem statePeriod_iff {m : ℕ}
    (W : ProductClosure.World.CompleteTiling
      (ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m)))
    (v : Contact.Cell (m+1)) :
    W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate v) ↔
      ∀ p, p ∈ W.tiles ↔ RegisteredPrime.AtlasPeriods.translate v p ∈ W.tiles := by
  constructor
  · intro h p
    constructor
    · intro hp
      exact h ▸ Set.mem_image_of_mem (RegisteredPrime.AtlasPeriods.translate v) hp
    · intro hp
      have hm : RegisteredPrime.AtlasPeriods.translate v p ∈
          RegisteredPrime.AtlasPeriods.translate v '' W.tiles := h.symm ▸ hp
      obtain ⟨q, hq, he⟩ := hm
      exact registered_translate_injective v he ▸ hq
  · intro h
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (h q).mp hq
    · intro hp
      refine ⟨RegisteredPrime.AtlasPeriods.translate (-v) p, ?_, registered_translate_cancel v p⟩
      apply (h _).mpr
      rwa [registered_translate_cancel]

/-- A decoded world's period is exactly a period of the original current
world, with the same integer vector and complete signed frame. -/
theorem fromWorld_period_iff {m : ℕ}
    (W : ProductClosure.World.CompleteTiling
      (ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m)))
    (v : Contact.Cell (m+1)) :
    (fromWorld W).IsPeriod v ↔ W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate v) := by
  rw [statePeriod_iff]
  constructor
  · intro h p
    have hp := h (toContact p)
    simpa only [mem_fromWorld, toRegistered_translatePose, toRegistered_toContact] using hp
  · intro h p
    change toRegistered p ∈ W.tiles ↔
      toRegistered (CarrierHierarchy.translatePose v p) ∈ W.tiles
    rw [toRegistered_translatePose]
    exact h (toRegistered p)

/-- Existing recovered worlds preserve exactly their complete state periods
when sent to the new finite-carrier interface. -/
theorem toWorld_period_iff {m : ℕ} (W : CarrierHierarchy.RegisteredWorld (m+1))
    (v : Contact.Cell (m+1)) :
    (toWorld W).HasStatePeriod (RegisteredPrime.AtlasPeriods.translate v) ↔ W.IsPeriod v := by
  rw [statePeriod_iff]
  constructor
  · intro h p
    have hp := h (toRegistered p)
    rw [← toRegistered_translatePose] at hp
    simpa only [mem_toWorld] using hp
  · intro h p
    have hp := h (toContact p)
    have he := (toRegistered_toContact p).symm
    rw [he]
    rw [← toRegistered_translatePose]
    simpa only [mem_toWorld] using hp

/-- Adapter endpoint: any recovered all-legal-world zero-period theorem can
be applied to every new complete world obeying the transported contact law. -/
theorem period_zero_transfer {m : ℕ} (L : Set (Contact.Pose (m+1)))
    (hzero : ∀ V : CarrierHierarchy.RegisteredWorld (m+1), V.Legal L →
      ∀ v, V.IsPeriod v → v = 0)
    (W : ProductClosure.World.CompleteTiling
      (ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m)))
    (hlegal : W.IsLegal ProductClosure.World.LatticeAdjacent (language L))
    (v : Contact.Cell (m+1))
    (hv : W.HasStatePeriod (RegisteredPrime.AtlasPeriods.translate v)) : v = 0 :=
  hzero (fromWorld W) (fromWorld_legal W L hlegal) v ((fromWorld_period_iff W v).mpr hv)

#print axioms fromWorld_period_iff
#print axioms toWorld_period_iff
#print axioms period_zero_transfer
end
end ClarkSeed.PoseAdapter
