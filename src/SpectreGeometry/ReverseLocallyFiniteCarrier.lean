module

public import SpectreGeometry.ReverseFiniteCarrierGluing
public import SpectreGeometry.ReverseClosedCoverStars
public import SpectreGeometry.ReverseCarrierLocalHomeomorph

@[expose] public section


/-! A closed, locally finite source cover with carrier-subspace homeomorphisms
and forward overlap agreement defines an actual continuous global map.
Incident inverse agreement and target-star interior then give local inversion. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set ReverseFinitePL
variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]

structure LocallyFiniteCarrierAtlas (X Y ι : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  source : ι → Set X
  target : ι → Set Y
  chart : ∀ i, source i ≃ₜ target i
  source_closed : ∀ i, IsClosed (source i)
  target_closed : ∀ i, IsClosed (target i)
  source_locallyFinite : LocallyFinite source
  source_cover : ∀ x, ∃ i, x ∈ source i
  forward_agree : ∀ i j x (hi : x ∈ source i) (hj : x ∈ source j),
    (chart i ⟨x,hi⟩ : Y) = (chart j ⟨x,hj⟩ : Y)

namespace LocallyFiniteCarrierAtlas
variable (A : LocallyFiniteCarrierAtlas X Y ι)

def map (x : X) : Y :=
  A.chart (Classical.choose (A.source_cover x)) ⟨x,Classical.choose_spec (A.source_cover x)⟩

theorem map_on (i : ι) (x : X) (hx : x ∈ A.source i) :
    A.map x = (A.chart i ⟨x,hx⟩ : Y) :=
  A.forward_agree _ i x (Classical.choose_spec (A.source_cover x)) hx

theorem continuous_map : Continuous A.map := by
  apply A.source_locallyFinite.continuous
  · ext x
    simp only [mem_iUnion,mem_univ,iff_true]
    exact A.source_cover x
  · exact A.source_closed
  · intro i
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h : Continuous (fun x : A.source i => (A.chart i x : Y)) :=
      continuous_subtype_val.comp (A.chart i).continuous
    exact h.congr (fun x => (A.map_on i x.val x.property).symm)

/-- Each whole carrier is mapped onto its prescribed target carrier. -/
theorem map_image_source (i : ι) : A.map '' A.source i = A.target i := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [A.map_on i x hx]
    exact (A.chart i ⟨x,hx⟩).property
  · intro hy
    let x := (A.chart i).symm ⟨y,hy⟩
    refine ⟨x.val,x.property,?_⟩
    rw [A.map_on i x.val x.property]
    exact congrArg Subtype.val ((A.chart i).apply_symm_apply ⟨y,hy⟩)

/-- Only carrier charts incident to a single source point need inverse agreement. -/
def IncidentInverseAgree : Prop :=
  ∀ x i j, x ∈ A.source i → x ∈ A.source j →
    ∀ y (hi : y ∈ A.target i) (hj : y ∈ A.target j),
      ((A.chart i).symm ⟨y,hi⟩ : X) = ((A.chart j).symm ⟨y,hj⟩ : X)

def targetStar (x : X) : Set Y := ⋃ i : {i // x ∈ A.source i}, A.target i.val

def starCharts (x : X) (hinv : A.IncidentInverseAgree) :
    ClosedCarrierChartFamily X Y {i // x ∈ A.source i} where
  source i := A.source i.val
  target i := A.target i.val
  chart i := A.chart i.val
  source_closed i := A.source_closed i.val
  target_closed i := A.target_closed i.val
  forward_agree i j y hi hj := A.forward_agree i.val j.val y hi hj
  inverse_agree i j y hi hj := hinv x i.val j.val i.property j.property y hi hj

def starHomeomorph (x : X) (hinv : A.IncidentInverseAgree) :
    incidentStar A.source x ≃ₜ A.targetStar x := by
  letI : Fintype {i // x ∈ A.source i} := (A.source_locallyFinite.point_finite x).fintype
  exact (A.starCharts x hinv).homeomorph

theorem starHomeomorph_agrees (x : X) (hinv : A.IncidentInverseAgree)
    (y : incidentStar A.source x) : A.map y = (A.starHomeomorph x hinv y : Y) := by
  letI : Fintype {i // x ∈ A.source i} := (A.source_locallyFinite.point_finite x).fintype
  obtain ⟨i,hi⟩ := mem_iUnion.mp y.property
  change A.map y.val = ((A.starCharts x hinv).homeomorph y).val
  rw [A.map_on i.val y.val hi,(A.starCharts x hinv).homeomorph_on i y hi]
  rfl

/-- Source-star interior follows from the source cover; the target-star
interior is the explicit finite-geometric certificate obligation. -/
theorem isLocalHomeomorph (hinv : A.IncidentInverseAgree)
    (htarget : ∀ x, A.map x ∈ interior (A.targetStar x)) : IsLocalHomeomorph A.map := by
  apply isLocalHomeomorph_of_carrier_charts A.map A.continuous_map
  intro x
  exact ⟨incidentStar A.source x,A.targetStar x,A.starHomeomorph x hinv,
    A.starHomeomorph_agrees x hinv,
    mem_interior_incidentStar A.source A.source_locallyFinite A.source_closed A.source_cover x,
    htarget x⟩

end LocallyFiniteCarrierAtlas
end
end SpectreGeometry.ReverseExistence
