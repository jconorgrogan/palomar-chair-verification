module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! A quantitative global inversion theorem for the parity deformation.
The geometric application must prove the residual Lipschitz estimate; no
homeomorphism or properness premise is supplied here. -/
namespace SpectreGeometry.Deformation
noncomputable section
open Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

set_option backward.privateInPublic true in
theorem translated_contracting {g : E → E} {q : ℝ≥0}
    (hq : q < 1) (hg : LipschitzWith q g) (y : E) :
    ContractingWith q (fun x => y + g x) := by
  refine ⟨hq,LipschitzWith.of_dist_le_mul fun x z => ?_⟩
  simpa only [dist_add_left] using hg.dist_le_mul x z

set_option backward.privateInPublic true in
/-- An identity-minus-strict-contraction map is a homeomorphism of every
complete normed additive group. The inverse is constructed by Banach's theorem. -/
def identitySubHomeomorph (g : E → E) (q : ℝ≥0)
    (hq : q < 1) (hg : LipschitzWith q g) : E ≃ₜ E where
  toFun x := x - g x
  invFun y := (translated_contracting hq hg y).fixedPoint (fun x => y + g x)
  left_inv x := by
    symm
    apply (translated_contracting hq hg (x-g x)).fixedPoint_unique
    change x - g x + g x = x
    exact sub_add_cancel _ _
  right_inv y := by
    have h := (translated_contracting hq hg y).fixedPoint_isFixedPt
    change y + g ((translated_contracting hq hg y).fixedPoint (fun x => y + g x)) = _ at h
    exact (eq_sub_iff_add_eq.mpr h).symm
  continuous_toFun := continuous_id.sub hg.continuous
  continuous_invFun := by
    have hh : LipschitzWith ((1-q)⁻¹)
        (fun y => (translated_contracting hq hg y).fixedPoint (fun x => y + g x)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      have h := (translated_contracting hq hg y).fixedPoint_lipschitz_in_map
        (translated_contracting hq hg z) (C := dist y z) (by
          intro x
          rw [dist_add_right])
      simpa only [NNReal.coe_inv,NNReal.coe_sub hq.le,NNReal.coe_one,div_eq_mul_inv,
        mul_comm] using h
    exact hh.continuous

@[simp] theorem identitySubHomeomorph_apply (g : E → E) (q : ℝ≥0)
    (hq : q < 1) (hg : LipschitzWith q g) (x : E) :
    identitySubHomeomorph g q hq hg x = x - g x := rfl

variable [NormedSpace ℝ E]

/-- A global residual bound for `x - F(x)/8` suffices. This formulation matches
the finite matrix certificate used by the physical parity deformation. -/
def ofEighthResidual (F : E → E) (q : ℝ≥0) (hq : q < 1)
    (hF : LipschitzWith q (fun x => x - (1/8 : ℝ) • F x)) : E ≃ₜ E :=
  (identitySubHomeomorph (fun x => x - (1/8 : ℝ) • F x) q hq hF).trans
    (Homeomorph.smulOfNeZero (8 : ℝ) (by norm_num))

@[simp] theorem ofEighthResidual_apply (F : E → E) (q : ℝ≥0) (hq : q < 1)
    (hF : LipschitzWith q (fun x => x - (1/8 : ℝ) • F x)) (x : E) :
    ofEighthResidual F q hq hF x = F x := by
  simp [ofEighthResidual,smul_smul]

end

section Transport
variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Coverage transports through a proved homeomorphism. -/
theorem cover_image (e : X ≃ₜ Y) (T : ι → Set X)
    (hcover : ∀ x, ∃ i, x ∈ T i) :
    ∀ y, ∃ i, y ∈ e '' T i := by
  intro y
  obtain ⟨i,hi⟩ := hcover (e.symm y)
  exact ⟨i,e.symm y,hi,e.apply_symm_apply y⟩

/-- Disjoint tile interiors transport exactly, rather than merely boundary data. -/
theorem disjoint_interiors_image (e : X ≃ₜ Y) (T : ι → Set X)
    (hdisjoint : Pairwise fun i j => Disjoint (interior (T i)) (interior (T j))) :
    Pairwise fun i j => Disjoint (interior (e '' T i)) (interior (e '' T j)) := by
  intro i j hij
  rw [←e.image_interior,←e.image_interior]
  exact (Set.disjoint_image_iff e.injective).2 (hdisjoint hij)

/-- Literal target carriers can replace the images once equality is proved. -/
theorem tiling_transport (e : X ≃ₜ Y) (T : ι → Set X) (U : ι → Set Y)
    (hcover : ∀ x, ∃ i, x ∈ T i)
    (hdisjoint : Pairwise fun i j => Disjoint (interior (T i)) (interior (T j)))
    (himage : ∀ i, e '' T i = U i) :
    (∀ y, ∃ i, y ∈ U i) ∧
      Pairwise (fun i j => Disjoint (interior (U i)) (interior (U j))) := by
  constructor
  · simpa only [himage] using cover_image e T hcover
  · simpa only [himage] using disjoint_interiors_image e T hdisjoint

end Transport
end SpectreGeometry.Deformation
