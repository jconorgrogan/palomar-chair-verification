module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocallyFinite

@[expose] public section


/-! Compatible homeomorphisms of finite closed carrier subspaces glue to a
homeomorphism of their unions. No ambient extension of any chart is assumed. -/
namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set
variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]

structure ClosedCarrierChartFamily (X Y ι : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  source : ι → Set X
  target : ι → Set Y
  chart : ∀ i, source i ≃ₜ target i
  source_closed : ∀ i, IsClosed (source i)
  target_closed : ∀ i, IsClosed (target i)
  forward_agree : ∀ i j x (hi : x ∈ source i) (hj : x ∈ source j),
    (chart i ⟨x,hi⟩ : Y) = (chart j ⟨x,hj⟩ : Y)
  inverse_agree : ∀ i j y (hi : y ∈ target i) (hj : y ∈ target j),
    ((chart i).symm ⟨y,hi⟩ : X) = ((chart j).symm ⟨y,hj⟩ : X)

namespace ClosedCarrierChartFamily
variable (D : ClosedCarrierChartFamily X Y ι)

def sourceCarrier : Set X := ⋃ i, D.source i
def targetCarrier : Set Y := ⋃ i, D.target i

def sourceChoice (x : D.sourceCarrier) : ι := Classical.choose (mem_iUnion.mp x.property)
def targetChoice (y : D.targetCarrier) : ι := Classical.choose (mem_iUnion.mp y.property)

theorem sourceChoice_mem (x : D.sourceCarrier) : x.val ∈ D.source (D.sourceChoice x) :=
  Classical.choose_spec (mem_iUnion.mp x.property)
theorem targetChoice_mem (y : D.targetCarrier) : y.val ∈ D.target (D.targetChoice y) :=
  Classical.choose_spec (mem_iUnion.mp y.property)

def forward (x : D.sourceCarrier) : D.targetCarrier :=
  let y := D.chart (D.sourceChoice x) ⟨x.val,D.sourceChoice_mem x⟩
  ⟨y.val,mem_iUnion.mpr ⟨D.sourceChoice x,y.property⟩⟩

def backward (y : D.targetCarrier) : D.sourceCarrier :=
  let x := (D.chart (D.targetChoice y)).symm ⟨y.val,D.targetChoice_mem y⟩
  ⟨x.val,mem_iUnion.mpr ⟨D.targetChoice y,x.property⟩⟩

theorem forward_on (i : ι) (x : D.sourceCarrier) (hx : x.val ∈ D.source i) :
    (D.forward x).val = (D.chart i ⟨x.val,hx⟩ : Y) :=
  D.forward_agree _ _ _ (D.sourceChoice_mem x) hx

theorem backward_on (i : ι) (y : D.targetCarrier) (hy : y.val ∈ D.target i) :
    (D.backward y).val = ((D.chart i).symm ⟨y.val,hy⟩ : X) :=
  D.inverse_agree _ _ _ (D.targetChoice_mem y) hy

theorem backward_forward (x : D.sourceCarrier) : D.backward (D.forward x) = x := by
  apply Subtype.ext
  let i := D.sourceChoice x
  have hx := D.sourceChoice_mem x
  have hy : (D.forward x).val ∈ D.target i := by
    rw [D.forward_on i x hx]
    exact (D.chart i ⟨x.val,hx⟩).property
  rw [D.backward_on i (D.forward x) hy]
  have he : (⟨(D.forward x).val,hy⟩ : D.target i) = D.chart i ⟨x.val,hx⟩ :=
    Subtype.ext (D.forward_on i x hx)
  rw [he,(D.chart i).symm_apply_apply]

theorem forward_backward (y : D.targetCarrier) : D.forward (D.backward y) = y := by
  apply Subtype.ext
  let i := D.targetChoice y
  have hy := D.targetChoice_mem y
  have hx : (D.backward y).val ∈ D.source i := by
    rw [D.backward_on i y hy]
    exact ((D.chart i).symm ⟨y.val,hy⟩).property
  rw [D.forward_on i (D.backward y) hx]
  have he : (⟨(D.backward y).val,hx⟩ : D.source i) = (D.chart i).symm ⟨y.val,hy⟩ :=
    Subtype.ext (D.backward_on i y hy)
  rw [he,(D.chart i).apply_symm_apply]

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
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hl : Continuous (fun x : C i => (⟨x.val.val,x.property⟩ : D.source i)) := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    have hh := continuous_subtype_val.comp ((D.chart i).continuous.comp hl)
    exact hh.congr (fun x => (D.forward_on i x.val x.property).symm)

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
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hl : Continuous (fun y : C i => (⟨y.val.val,y.property⟩ : D.target i)) := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    have hh := continuous_subtype_val.comp ((D.chart i).symm.continuous.comp hl)
    exact hh.congr (fun y => (D.backward_on i y.val y.property).symm)

def homeomorph [Finite ι] : D.sourceCarrier ≃ₜ D.targetCarrier where
  toFun := D.forward
  invFun := D.backward
  left_inv := D.backward_forward
  right_inv := D.forward_backward
  continuous_toFun := D.continuous_forward
  continuous_invFun := D.continuous_backward

@[simp] theorem homeomorph_on [Finite ι] (i : ι) (x : D.sourceCarrier)
    (hx : x.val ∈ D.source i) : (D.homeomorph x).val = (D.chart i ⟨x.val,hx⟩ : Y) :=
  D.forward_on i x hx

end ClosedCarrierChartFamily
end
end SpectreGeometry.ReverseFinitePL
