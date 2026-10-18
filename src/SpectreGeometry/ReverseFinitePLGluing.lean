module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocallyFinite

@[expose] public section


/-! Finite closed pieces with compatible forward and inverse charts glue to
an actual homeomorphism of their entire carriers. Coverage is by the defining
unions, rather than an interior-only or boundary-only claim. -/
namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Compatibility data for a finite piecewise homeomorphism. The inverse
compatibility is an explicit obligation, so global injectivity is proved. -/
structure ClosedChartFamily (X Y ι : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  source : ι → Set X
  target : ι → Set Y
  chart : ι → X ≃ₜ Y
  source_closed : ∀ i, IsClosed (source i)
  target_closed : ∀ i, IsClosed (target i)
  image_source : ∀ i, chart i '' source i = target i
  forward_agree : ∀ i j x, x ∈ source i → x ∈ source j → chart i x = chart j x
  inverse_agree : ∀ i j y, y ∈ target i → y ∈ target j → (chart i).symm y = (chart j).symm y

namespace ClosedChartFamily
variable (D : ClosedChartFamily X Y ι)

def sourceCarrier : Set X := ⋃ i, D.source i
def targetCarrier : Set Y := ⋃ i, D.target i

def sourceChoice (x : D.sourceCarrier) : ι := Classical.choose (mem_iUnion.mp x.property)
def targetChoice (y : D.targetCarrier) : ι := Classical.choose (mem_iUnion.mp y.property)

theorem sourceChoice_mem (x : D.sourceCarrier) : x.val ∈ D.source (D.sourceChoice x) :=
  Classical.choose_spec (mem_iUnion.mp x.property)
theorem targetChoice_mem (y : D.targetCarrier) : y.val ∈ D.target (D.targetChoice y) :=
  Classical.choose_spec (mem_iUnion.mp y.property)

def forward (x : D.sourceCarrier) : D.targetCarrier :=
  ⟨D.chart (D.sourceChoice x) x.val, mem_iUnion.mpr ⟨D.sourceChoice x,
    D.image_source (D.sourceChoice x) ▸ mem_image_of_mem _ (D.sourceChoice_mem x)⟩⟩

def backward (y : D.targetCarrier) : D.sourceCarrier :=
  ⟨(D.chart (D.targetChoice y)).symm y.val, by
    let i := D.targetChoice y
    have hy : y.val ∈ D.chart i '' D.source i := by rw [D.image_source]; exact D.targetChoice_mem y
    obtain ⟨x,hx,hxy⟩ := hy
    refine mem_iUnion.mpr ⟨i,?_⟩
    change (D.chart i).symm y.val ∈ D.source i
    simpa [←hxy] using hx⟩

theorem forward_on (i : ι) (x : D.sourceCarrier) (hx : x.val ∈ D.source i) :
    (D.forward x).val = D.chart i x.val :=
  D.forward_agree _ _ _ (D.sourceChoice_mem x) hx

theorem backward_on (i : ι) (y : D.targetCarrier) (hy : y.val ∈ D.target i) :
    (D.backward y).val = (D.chart i).symm y.val :=
  D.inverse_agree _ _ _ (D.targetChoice_mem y) hy

theorem backward_forward (x : D.sourceCarrier) : D.backward (D.forward x) = x := by
  apply Subtype.ext
  let i := D.sourceChoice x
  have hx := D.sourceChoice_mem x
  have hy : (D.forward x).val ∈ D.target i := by
    rw [D.forward_on i x hx,←D.image_source]
    exact mem_image_of_mem _ hx
  rw [D.backward_on i (D.forward x) hy,D.forward_on i x hx]
  exact (D.chart i).symm_apply_apply x.val

theorem forward_backward (y : D.targetCarrier) : D.forward (D.backward y) = y := by
  apply Subtype.ext
  let i := D.targetChoice y
  have hy := D.targetChoice_mem y
  have hx : (D.backward y).val ∈ D.source i := by
    rw [D.backward_on i y hy]
    have h : y.val ∈ D.chart i '' D.source i := by rwa [D.image_source]
    obtain ⟨x,hx,hxy⟩ := h
    simpa [←hxy] using hx
  rw [D.forward_on i (D.backward y) hx,D.backward_on i y hy]
  exact (D.chart i).apply_symm_apply y.val

theorem continuous_forward [Finite ι] : Continuous D.forward := by
  apply Continuous.subtype_mk
  let C : ι → Set D.sourceCarrier := fun i => Subtype.val ⁻¹' D.source i
  apply (locallyFinite_of_finite C).continuous
  · ext x
    simp only [mem_iUnion,mem_univ,iff_true]
    change ∃ i, x.val ∈ D.source i
    exact mem_iUnion.mp x.property
  · intro i
    exact (D.source_closed i).preimage continuous_subtype_val
  · intro i
    apply ((D.chart i).continuous.comp continuous_subtype_val).continuousOn.congr
    intro x hx
    exact D.forward_on i x hx

theorem continuous_backward [Finite ι] : Continuous D.backward := by
  apply Continuous.subtype_mk
  let C : ι → Set D.targetCarrier := fun i => Subtype.val ⁻¹' D.target i
  apply (locallyFinite_of_finite C).continuous
  · ext y
    simp only [mem_iUnion,mem_univ,iff_true]
    change ∃ i, y.val ∈ D.target i
    exact mem_iUnion.mp y.property
  · intro i
    exact (D.target_closed i).preimage continuous_subtype_val
  · intro i
    apply ((D.chart i).symm.continuous.comp continuous_subtype_val).continuousOn.congr
    intro y hy
    exact D.backward_on i y hy

/-- The finite charts determine a homeomorphism of the full closed carriers. -/
def homeomorph [Finite ι] : D.sourceCarrier ≃ₜ D.targetCarrier where
  toFun := D.forward
  invFun := D.backward
  left_inv := D.backward_forward
  right_inv := D.forward_backward
  continuous_toFun := D.continuous_forward
  continuous_invFun := D.continuous_backward

@[simp] theorem homeomorph_on [Finite ι] (i : ι) (x : D.sourceCarrier)
    (hx : x.val ∈ D.source i) : (D.homeomorph x).val = D.chart i x.val := D.forward_on i x hx

end ClosedChartFamily
end
end SpectreGeometry.ReverseFinitePL
