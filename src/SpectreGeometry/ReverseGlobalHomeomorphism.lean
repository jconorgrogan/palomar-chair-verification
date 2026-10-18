module

public import SpectreGeometry.ReverseProperCovering
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section


/-! Global inversion for proper local homeomorphisms, with a concrete plane
specialization and an application-ready bounded-distance criterion.
No registration, finite-cluster coverage, or local star theorem is assumed to
have been proved here. Such geometry must supply the local-homeomorphism and
bounded-distance hypotheses. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set Function

/-- A covering of a simply connected, locally path-connected target by a
nonempty connected source admits a continuous two-sided inverse. -/
theorem exists_continuous_inverse_of_covering
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PreconnectedSpace X] [Nonempty X]
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
    {F : X → Y} (hC : IsCoveringMap F) :
    ∃ G : C(Y, X), LeftInverse G F ∧ RightInverse G F := by
  let x₀ : X := Classical.choice inferInstance
  obtain ⟨G, ⟨hG₀, hFG⟩, _⟩ :=
    hC.existsUnique_continuousMap_lifts (ContinuousMap.id Y) (F x₀) x₀ rfl
  have hGF : (G : Y → X) ∘ F = id := by
    apply hC.eq_of_comp_eq (G.continuous.comp hC.continuous) continuous_id _ x₀ hG₀
    funext x
    exact congrFun hFG (F x)
  exact ⟨G, fun x => congrFun hGF x, fun y => congrFun hFG y⟩

/-- The homeomorphism whose forward map is a given proper local homeomorphism. -/
def homeomorphOfProperLocalHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [PreconnectedSpace X] [Nonempty X]
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (F : X → Y) (hP : IsProperMap F) (hL : IsLocalHomeomorph F) : X ≃ₜ Y := by
  let h := exists_continuous_inverse_of_covering
    (isCoveringMap_of_proper_local_homeomorph hP hL)
  exact { toFun := F
          invFun := h.choose
          left_inv := h.choose_spec.1
          right_inv := h.choose_spec.2
          continuous_toFun := hP.continuous
          continuous_invFun := h.choose.continuous }

@[simp] theorem homeomorphOfProperLocalHomeomorph_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [PreconnectedSpace X] [Nonempty X]
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (F : X → Y) (hP : IsProperMap F) (hL : IsLocalHomeomorph F) (x : X) :
    homeomorphOfProperLocalHomeomorph F hP hL x = F x := rfl

/-- A proper local homeomorphism of the plane is a homeomorphism. -/
def planeHomeomorphOfProperLocalHomeomorph
    (F : ℝ × ℝ → ℝ × ℝ) (hP : IsProperMap F) (hL : IsLocalHomeomorph F) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := homeomorphOfProperLocalHomeomorph F hP hL

@[simp] theorem planeHomeomorphOfProperLocalHomeomorph_apply
    (F : ℝ × ℝ → ℝ × ℝ) (hP : IsProperMap F) (hL : IsLocalHomeomorph F) (x : ℝ × ℝ) :
    planeHomeomorphOfProperLocalHomeomorph F hP hL x = F x := rfl

/-- The global assembly interface for finite cluster maps near an auxiliary
anchor homeomorphism. Continuity follows from the local-homeomorphism input. -/
def planeHomeomorphOfBoundedDistance
    (F : ℝ × ℝ → ℝ × ℝ) (hL : IsLocalHomeomorph F)
    (H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (C : ℝ)
    (hC : ∀ x, dist (F x) (H x) ≤ C) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  planeHomeomorphOfProperLocalHomeomorph F
    (isProperMap_of_bounded_distance_homeomorph H hL.continuous (0, 0) C hC) hL

@[simp] theorem planeHomeomorphOfBoundedDistance_apply
    (F : ℝ × ℝ → ℝ × ℝ) (hL : IsLocalHomeomorph F)
    (H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (C : ℝ)
    (hC : ∀ x, dist (F x) (H x) ≤ C) (x : ℝ × ℝ) :
    planeHomeomorphOfBoundedDistance F hL H C hC x = F x := rfl

/-- Propositional form of the application-ready global criterion. -/
theorem isHomeomorph_of_bounded_distance
    (F : ℝ × ℝ → ℝ × ℝ) (hL : IsLocalHomeomorph F)
    (H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (C : ℝ)
    (hC : ∀ x, dist (F x) (H x) ≤ C) : IsHomeomorph F :=
  (planeHomeomorphOfBoundedDistance F hL H C hC).isHomeomorph

end
end SpectreGeometry.ReverseExistence
