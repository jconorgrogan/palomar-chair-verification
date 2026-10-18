module

public import SpectreGeometry.PhysicalGridRealization
public import SpectreGeometry.DeformationHomeomorphismCarrierPeriod
public import SpectreClusters.GridFieldTranslations

@[expose] public section


/-! Every ordinary physical carrier period induces an actual nonzero integer
translation covariance of the extracted literal kite-grid ownership field. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreClusters.DeformedLiteralBinding SpectreGeometry.Deformation

def gridCenterMapReal : SpectreClusters.Point →+ RealPoint where
  toFun p := gridEmbeddingLinear (integerPoint (lattice p))
  map_zero' := by simp [lattice,integerPoint,gridEmbeddingLinear]
  map_add' p q := by
    change gridEmbeddingLinear (integerPoint (lattice (SpectreClusters.add p q))) = _
    rw [lattice_add,integerPoint_add,map_add]

theorem gridCenterMapReal_injective : Function.Injective gridCenterMapReal := by
  intro p q hpq
  apply lattice_injective
  have h : integerPoint (lattice p) = integerPoint (lattice q) :=
    gridEmbeddingHomeomorph.injective hpq
  apply Prod.ext
  · have hx : ((lattice p).1 : ℝ) = ((lattice q).1 : ℝ) := congrArg Prod.fst h
    exact_mod_cast hx
  · have hy : ((lattice p).2 : ℝ) = ((lattice q).2 : ℝ) := congrArg Prod.snd h
    exact_mod_cast hy

theorem reflectCenter_sub_realization (p q : SpectreClusters.Point) :
    reflectCenter (p-q) = reflectCenter p-reflectCenter q := by
  apply Prod.ext <;> simp [reflectCenter] <;> ring

theorem reflectCenter_injective_realization : Function.Injective reflectCenter := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> simp only [reflectCenter] at hx hy ⊢ <;> omega

section Tiling
variable {ι : Type*} (f : ι → EPlane ≃ᵢ EPlane)
  (hdirect : ∀ i, DirectPlacement (f i))
  (hdisjoint : Pairwise fun i j =>
    Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
  (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root : ι)

/-- The concrete deformation followed by the common literal grid coordinates. -/
def physicalToGridHomeomorph : EPlane ≃ₜ RealPoint :=
  (physicalHomeomorph f hdirect hdisjoint hcover root).trans
    (gridPhysicalHomeomorph (tilingGridOrigin f hdirect hdisjoint hcover root)).symm

theorem physicalToGridHomeomorph_image_tile (i : ι) :
    physicalToGridHomeomorph f hdirect hdisjoint hcover root '' (f i '' euclideanBody) =
      placementKiteBody (tilingGridPlacement f hdirect hdisjoint hcover root i) := by
  change (fun x => (gridPhysicalHomeomorph (tilingGridOrigin f hdirect hdisjoint hcover root)).symm
    (physicalHomeomorph f hdirect hdisjoint hcover root x)) '' (f i '' euclideanBody) = _
  rw [←Set.image_image,physicalHomeomorph_image_tile,
    ←tilingGrid_image_body f hdirect hdisjoint hcover root i]
  exact (gridPhysicalHomeomorph (tilingGridOrigin f hdirect hdisjoint hcover root)).symm_image_image _

theorem tilingLatticeCoordinate_translation_difference (i j r : ι) (v : EPlane)
    (hij : ∀ p, f j p = f i p+v) (hr : ∀ p, f r p = f root p+v) :
    tilingLatticeCoordinate f hdirect hdisjoint hcover root j-
      tilingLatticeCoordinate f hdirect hdisjoint hcover root i =
    tilingLatticeCoordinate f hdirect hdisjoint hcover root r-
      tilingLatticeCoordinate f hdirect hdisjoint hcover root root := by
  apply gridCenterMapReal_injective
  rw [map_sub,map_sub]
  have hd := tilingTargetOrigin_translation_difference f hdirect hdisjoint hcover root i j r v
    (hij 0) (hr 0)
  have hstep (a b : ι) (hab : ∀ p, f b p = f a p+v) :
      gridCenterMapReal (tilingLatticeCoordinate f hdirect hdisjoint hcover root b)-
        gridCenterMapReal (tilingLatticeCoordinate f hdirect hdisjoint hcover root a) =
      tilingTargetOrigin f hdirect hdisjoint hcover root b-
        tilingTargetOrigin f hdirect hdisjoint hcover root a := by
    have ha := tilingGrid_anchor_real f hdirect hdisjoint hcover root a
    have hb := tilingGrid_anchor_real f hdirect hdisjoint hcover root b
    rw [←tilingFrame_translation f hdirect hdisjoint hcover root a b v hab] at hb
    change tilingGridOrigin f hdirect hdisjoint hcover root+
      gridCenterMapReal (tilingLatticeCoordinate f hdirect hdisjoint hcover root a) = _ at ha
    change tilingGridOrigin f hdirect hdisjoint hcover root+
      gridCenterMapReal (tilingLatticeCoordinate f hdirect hdisjoint hcover root b) = _ at hb
    calc
      _ = (tilingGridOrigin f hdirect hdisjoint hcover root+
          gridCenterMapReal (tilingLatticeCoordinate f hdirect hdisjoint hcover root b))-
        (tilingGridOrigin f hdirect hdisjoint hcover root+
          gridCenterMapReal (tilingLatticeCoordinate f hdirect hdisjoint hcover root a)) := by abel
      _ = _ := by rw [ha,hb]; abel
  rw [hstep i j hij,hstep root r hr,hd]

theorem tilingGridPlacement_translation (i j r : ι) (v : EPlane)
    (hij : ∀ p, f j p = f i p+v) (hr : ∀ p, f r p = f root p+v) :
    tilingGridPlacement f hdirect hdisjoint hcover root j =
      movePlacement 0 ((tilingGridPlacement f hdirect hdisjoint hcover root r).center-
        (tilingGridPlacement f hdirect hdisjoint hcover root root).center)
        (tilingGridPlacement f hdirect hdisjoint hcover root i) := by
  have hk := tilingFrame_translation f hdirect hdisjoint hcover root i j v hij
  have hz := tilingLatticeCoordinate_translation_difference f hdirect hdisjoint hcover root i j r v hij hr
  have hc := congrArg reflectCenter hz
  rw [reflectCenter_sub_realization,reflectCenter_sub_realization] at hc
  simp only [tilingGridPlacement,movePlacement,turnAdd_zero,SpectreClusters.rotate]
  rw [←hk]
  congr 1
  change reflectCenter (tilingLatticeCoordinate f hdirect hdisjoint hcover root j) =
    (reflectCenter (tilingLatticeCoordinate f hdirect hdisjoint hcover root r)-
      reflectCenter (tilingLatticeCoordinate f hdirect hdisjoint hcover root root))+
      reflectCenter (tilingLatticeCoordinate f hdirect hdisjoint hcover root i)
  exact sub_eq_iff_eq_add.mp hc

theorem tilingGridPlacement_translation_nonzero (r : ι) (v : EPlane) (hv : v ≠ 0)
    (hr : ∀ p, f r p = f root p+v) :
    (tilingGridPlacement f hdirect hdisjoint hcover root r).center-
      (tilingGridPlacement f hdirect hdisjoint hcover root root).center ≠ 0 := by
  intro hzero
  have hz : tilingLatticeCoordinate f hdirect hdisjoint hcover root r =
      tilingLatticeCoordinate f hdirect hdisjoint hcover root root :=
    reflectCenter_injective_realization (sub_eq_zero.mp hzero)
  have hk := tilingFrame_translation f hdirect hdisjoint hcover root root r v hr
  have ha := tilingGrid_anchor_real f hdirect hdisjoint hcover root root
  have hb := tilingGrid_anchor_real f hdirect hdisjoint hcover root r
  rw [hz,←hk] at hb
  have ho : tilingTargetOrigin f hdirect hdisjoint hcover root r =
      tilingTargetOrigin f hdirect hdisjoint hcover root root := add_right_cancel (hb.symm.trans ha)
  have he : f r (euclideanCoordinates (realVertex 0)) = f root (euclideanCoordinates (realVertex 0)) := by
    apply (physicalHomeomorph f hdirect hdisjoint hcover root).injective
    rw [physicalHomeomorph_on_tile f hdirect hdisjoint hcover root r _ (source_vertex_mem_body 0),
      physicalHomeomorph_on_tile f hdirect hdisjoint hcover root root _ (source_vertex_mem_body 0),ho,←hk]
  rw [hr] at he
  exact hv (by simpa using he)

theorem physicalGridField_period_of_placement_period (u : SpectreClusters.Point)
    (hu : ∀ i, ∃ j, tilingGridPlacement f hdirect hdisjoint hcover root j =
      movePlacement 0 u (tilingGridPlacement f hdirect hdisjoint hcover root i)) :
    GridFieldTranslationPeriod (physicalGridField f hdirect hdisjoint hcover root) u := by
  intro c
  let p := tilingGridPlacement f hdirect hdisjoint hcover root
  let hc := (homochiral_literal_kite_tiling f hdirect hdisjoint hcover root).1
  let i := probeOwner p hc c
  obtain ⟨j,hj⟩ := hu i
  have hm : moveCell 0 u c ∈ placementCells (p j) := by
    rw [show p j = movePlacement 0 u (p i) from hj,placementCells_moved]
    exact List.mem_map.mpr ⟨c,probeOwner_contains p hc c,rfl⟩
  have he := physicalGridField_owns f hdirect hdisjoint hcover root j (moveCell 0 u c) hm
  rw [hj] at he
  exact he

/-- Any nonzero ordinary physical period produces a nonzero integer period
of the actual extracted grid field, retaining literal tile ownership. -/
theorem physical_carrier_period_to_grid_period (v : EPlane) (hv : v ≠ 0)
    (hperiod : CarrierTranslationPeriod f v) :
    ∃ u : SpectreClusters.Point, u ≠ 0 ∧
      GridFieldTranslationPeriod (physicalGridField f hdirect hdisjoint hcover root) u := by
  have hs := carrier_period_recovers_slots f hdirect v hperiod
  obtain ⟨r,hr⟩ := hs root
  let u := (tilingGridPlacement f hdirect hdisjoint hcover root r).center-
    (tilingGridPlacement f hdirect hdisjoint hcover root root).center
  refine ⟨u,tilingGridPlacement_translation_nonzero f hdirect hdisjoint hcover root r v hv hr,?_⟩
  apply physicalGridField_period_of_placement_period f hdirect hdisjoint hcover root u
  intro i
  obtain ⟨j,hj⟩ := hs i
  exact ⟨j,tilingGridPlacement_translation f hdirect hdisjoint hcover root i j r v hj hr⟩

theorem physical_collection_period_to_grid_period (v : EPlane) (hv : v ≠ 0)
    (hperiod : CarrierCollectionPeriod f v) :
    ∃ u : SpectreClusters.Point, u ≠ 0 ∧
      GridFieldTranslationPeriod (physicalGridField f hdirect hdisjoint hcover root) u :=
  physical_carrier_period_to_grid_period f hdirect hdisjoint hcover root v hv
    (carrierCollectionPeriod_implies_translationPeriod f v hperiod)

end Tiling

/-- Root selection is internal: an ordinary nonzero physical carrier period
forces a valid genuinely periodic literal grid ownership field. -/
theorem homochiral_physical_period_has_valid_periodic_grid {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j => Disjoint (interior (f i '' euclideanBody))
      (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (v : EPlane) (hv : v ≠ 0) (hperiod : CarrierCollectionPeriod f v) :
    ∃ g : Cell → HTPlacement, ValidGridField g ∧
      ∃ u : SpectreClusters.Point, u ≠ 0 ∧ GridFieldTranslationPeriod g u := by
  obtain ⟨root,_⟩ := hcover 0
  exact ⟨physicalGridField f hdirect hdisjoint hcover root,
    physicalGridField_valid f hdirect hdisjoint hcover root,
    physical_collection_period_to_grid_period f hdirect hdisjoint hcover root v hv hperiod⟩

end
end SpectreGeometry
