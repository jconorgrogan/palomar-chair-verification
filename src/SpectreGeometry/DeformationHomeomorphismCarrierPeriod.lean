module

public import SpectreGeometry.DeformationHomeomorphismRigidity
public import SpectreGeometry.DeformationHomeomorphismPeriod

@[expose] public section


/-! Ordinary, unlabelled carrier periods recover source slots intrinsically
and are transported to nonzero translations by the actual homeomorphism. -/
namespace SpectreGeometry.Deformation
noncomputable section
open Set

def translatedPlacement (f : EPlane ≃ᵢ EPlane) (v : EPlane) : EPlane ≃ᵢ EPlane :=
  f.trans (IsometryEquiv.addRight v)

@[simp] theorem translatedPlacement_apply (f : EPlane ≃ᵢ EPlane) (v x : EPlane) :
    translatedPlacement f v x = f x+v := rfl

theorem translatedPlacement_direct (f : EPlane ≃ᵢ EPlane) (hf : DirectPlacement f)
    (v : EPlane) : DirectPlacement (translatedPlacement f v) := by
  have hc (x : RealPoint) : coordinateAction (translatedPlacement f v) x = coordinateAction f x := by
    rw [coordinateAction_apply, coordinateAction_apply]
    change coordinateLinearEquiv.symm (f (euclideanCoordinates x)+v) -
      coordinateLinearEquiv.symm (f 0+v) = _
    rw [map_add,map_add]
    abel
  unfold DirectPlacement frameFirst frameSecond at *
  rw [hc,hc]
  exact hf

theorem carrier_translation_recovers_placement (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) (v : EPlane)
    (hbody : g '' euclideanBody = (fun x : EPlane => x+v) '' (f '' euclideanBody)) :
    ∀ p : EPlane, g p = f p+v := by
  have he : g = translatedPlacement f v := direct_placement_eq_of_carrier_eq g
    (translatedPlacement f v) hg (translatedPlacement_direct f hf v) (by
      rw [hbody,Set.image_image]
      rfl)
  intro p
  rw [he,translatedPlacement_apply]

/-- Ordinary translation preservation of the actual geometric carriers,
with no matching of labelled vertices or finite orientation slots. -/
def CarrierTranslationPeriod {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane) (v : EPlane) : Prop :=
  ∀ i, ∃ j, f j '' euclideanBody = (fun x : EPlane => x+v) '' (f i '' euclideanBody)

/-- Equality of the unlabelled collections of translated and original carriers. -/
def CarrierCollectionPeriod {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane) (v : EPlane) : Prop :=
  Set.range (fun i => (fun x : EPlane => x+v) '' (f i '' euclideanBody)) =
    Set.range (fun i => f i '' euclideanBody)

theorem carrierCollectionPeriod_implies_translationPeriod {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (v : EPlane) (h : CarrierCollectionPeriod f v) :
    CarrierTranslationPeriod f v := by
  intro i
  have hi : (fun x : EPlane => x+v) '' (f i '' euclideanBody) ∈
      Set.range (fun i => f i '' euclideanBody) := h ▸ ⟨i,rfl⟩
  exact hi

theorem carrier_period_recovers_slots {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
    (hdirect : ∀ i, DirectPlacement (f i)) (v : EPlane)
    (hperiod : CarrierTranslationPeriod f v) :
    ∀ i, ∃ j, ∀ p : EPlane, f j p = f i p+v := by
  intro i
  obtain ⟨j,hj⟩ := hperiod i
  exact ⟨j,carrier_translation_recovers_placement (f i) (f j) (hdirect i) (hdirect j) v hj⟩

/-- An equivariant map transports ordinary collections of geometric carriers. -/
theorem carrier_collection_translation_transport {ι : Type*}
    (c d : ι → Set EPlane) (F : EPlane → EPlane) (v w : EPlane)
    (himage : ∀ i, F '' c i = d i) (htranslate : ∀ x, F (x+v)=F x+w)
    (hcollection : Set.range (fun i => (fun x : EPlane => x+v) '' c i) = Set.range c) :
    Set.range (fun i => (fun x : EPlane => x+w) '' d i) = Set.range d := by
  have he (i : ι) : (fun x : EPlane => x+w) '' d i =
      F '' ((fun x : EPlane => x+v) '' c i) := by
    rw [←himage i,Set.image_image,Set.image_image]
    congr 1
    funext x
    exact (htranslate x).symm
  ext s
  constructor
  · rintro ⟨i,rfl⟩
    have hi : (fun x : EPlane => x+v) '' c i ∈ Set.range c := hcollection ▸ ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := hi
    refine ⟨j,?_⟩
    dsimp only
    rw [he,←himage j,hj]
  · rintro ⟨i,rfl⟩
    have hi : c i ∈ Set.range (fun i => (fun x : EPlane => x+v) '' c i) :=
      hcollection.symm ▸ ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := hi
    refine ⟨j,?_⟩
    dsimp only at hj ⊢
    rw [he,hj,himage]

section Tiling
variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root : ι)

theorem physicalHomeomorph_carrier_translation (v : EPlane)
    (hperiod : CarrierTranslationPeriod f v) :
    ∃ w : EPlane, ∀ x : EPlane,
      physicalHomeomorph f hdirect hdisjoint hcover root (x+v) =
        physicalHomeomorph f hdirect hdisjoint hcover root x+w :=
  physicalHomeomorph_translation f hdirect hdisjoint hcover root v
    (carrier_period_recovers_slots f hdirect v hperiod)

theorem physicalHomeomorph_nonzero_carrier_translation (v : EPlane) (hv : v ≠ 0)
    (hperiod : CarrierTranslationPeriod f v) :
    ∃ w : EPlane, w ≠ 0 ∧ ∀ x : EPlane,
      physicalHomeomorph f hdirect hdisjoint hcover root (x+v) =
        physicalHomeomorph f hdirect hdisjoint hcover root x+w :=
  physicalHomeomorph_nonzero_translation f hdirect hdisjoint hcover root v hv
    (carrier_period_recovers_slots f hdirect v hperiod)

theorem physicalHomeomorph_nonzero_collection_translation (v : EPlane) (hv : v ≠ 0)
    (hperiod : CarrierCollectionPeriod f v) :
    ∃ w : EPlane, w ≠ 0 ∧ ∀ x : EPlane,
      physicalHomeomorph f hdirect hdisjoint hcover root (x+v) =
        physicalHomeomorph f hdirect hdisjoint hcover root x+w :=
  physicalHomeomorph_nonzero_carrier_translation f hdirect hdisjoint hcover root v hv
    (carrierCollectionPeriod_implies_translationPeriod f v hperiod)

/-- A nonzero ordinary carrier-collection period becomes a nonzero period
of the literal developed carriers, under the actual plane homeomorphism. -/
theorem developed_carrier_collection_nonzero_period (v : EPlane) (hv : v ≠ 0)
    (hperiod : CarrierCollectionPeriod f v) :
    ∃ w : EPlane, w ≠ 0 ∧
      (∀ x : EPlane, physicalHomeomorph f hdirect hdisjoint hcover root (x+v) =
        physicalHomeomorph f hdirect hdisjoint hcover root x+w) ∧
      Set.range (fun i => (fun x : EPlane => x+w) ''
        developedPlacedBody f hdirect hdisjoint hcover root i) =
        Set.range (developedPlacedBody f hdirect hdisjoint hcover root) := by
  obtain ⟨w,hw,he⟩ := physicalHomeomorph_nonzero_collection_translation
    f hdirect hdisjoint hcover root v hv hperiod
  exact ⟨w,hw,he,carrier_collection_translation_transport _ _ _ v w
    (physicalHomeomorph_image_tile f hdirect hdisjoint hcover root) he hperiod⟩

end Tiling
end
end SpectreGeometry.Deformation
