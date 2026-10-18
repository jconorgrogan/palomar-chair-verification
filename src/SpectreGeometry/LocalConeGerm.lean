module

public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv
public import Mathlib.Tactic.Abel

@[expose] public section


/-! Local body membership in every displacement direction, together with
product and affine transport. The predicate itself does not assert that the
model set is conic, nor does it assign an angular or solid-angle measure.
No orientation or factor-preservation assumption occurs in the isometry
transport theorem. -/
namespace SpectreGeometry
noncomputable section
open Set

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Near the zero displacement, membership in the body agrees with membership
in its specified local cone. This includes every direction and the origin. -/
def LocalConeGerm (S : Set E) (x : E) (C : Set E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ 0 ∈ U ∧ ∀ v ∈ U, x + v ∈ S ↔ v ∈ C

namespace LocalConeGerm

variable {S C : Set E} {x : E} {T D : Set F} {y : F}

/-- Local body germs multiply in the product topology. -/
theorem prod (hS : LocalConeGerm S x C) (hT : LocalConeGerm T y D) :
    LocalConeGerm (S ×ˢ T) (x, y) (C ×ˢ D) := by
  obtain ⟨U, hU, hU0, hS⟩ := hS
  obtain ⟨V, hV, hV0, hT⟩ := hT
  refine ⟨U ×ˢ V, hU.prod hV, ⟨hU0, hV0⟩, ?_⟩
  intro v hv
  exact and_congr (hS v.1 hv.1) (hT v.2 hv.2)

/-- Transport by an equivalence whose displacement action is a continuous
linear equivalence. Only this displacement identity is needed. -/
theorem map_equiv_of_displacement (h : LocalConeGerm S x C)
    (f : E ≃ F) (L : E ≃L[ℝ] F)
    (hadd : ∀ p v : E, f (p + v) = f p + L v) :
    LocalConeGerm (f '' S) (f x) (L '' C) := by
  obtain ⟨U, hU, hU0, hmem⟩ := h
  refine ⟨L '' U, L.isOpenMap U hU, ?_, ?_⟩
  · exact ⟨0, hU0, L.map_zero⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [← hadd x v]
    constructor
    · rintro ⟨p, hp, he⟩
      have hp' : x + v ∈ S := by rwa [f.injective he] at hp
      exact ⟨v, (hmem v hv).mp hp', rfl⟩
    · rintro ⟨w, hw, he⟩
      have hv' : v ∈ C := by rwa [L.injective he] at hw
      exact ⟨x + v, (hmem v hv).mpr hv', rfl⟩

/-- In particular, arbitrary continuous linear changes of coordinates
preserve the full local body germ, without any norm-preservation hypothesis. -/
theorem map_continuousLinearEquiv (h : LocalConeGerm S x C)
    (L : E ≃L[ℝ] F) :
    LocalConeGerm (L '' S) (L x) (L '' C) :=
  h.map_equiv_of_displacement L.toLinearEquiv.toEquiv L (fun p v => L.map_add p v)

/-- The linear part of an arbitrary continuous affine equivalence gives its
actual action on the germ's displacement vectors. -/
theorem map_continuousAffineEquiv (h : LocalConeGerm S x C)
    (f : E ≃ᴬ[ℝ] F) :
    LocalConeGerm (f '' S) (f x) (f.toAffineEquiv.linear '' C) := by
  let L : E ≃L[ℝ] F :=
    { f.toAffineEquiv.linear with
      continuous_toFun := f.toContinuousAffineMap.contLinear.continuous
      continuous_invFun := f.symm.toContinuousAffineMap.contLinear.continuous }
  apply h.map_equiv_of_displacement f.toEquiv L
  intro p v
  change f.toAffineEquiv (p + v) = f.toAffineEquiv p + f.toAffineEquiv.linear v
  simpa only [vadd_eq_add, add_comm] using f.toAffineEquiv.map_vadd p v

/-- Affine-equivalence form with precisely the continuity assumptions needed
in an arbitrary real normed vector space. -/
theorem map_affineEquiv (h : LocalConeGerm S x C) (f : E ≃ᵃ[ℝ] F)
    (hf : Continuous f) (hfinv : Continuous f.symm) :
    LocalConeGerm (f '' S) (f x) (f.linear '' C) := by
  let g : E ≃ᴬ[ℝ] F :=
    { f with continuous_toFun := hf, continuous_invFun := hfinv }
  exact h.map_continuousAffineEquiv g

/-- A linear isometry transports the cone by the same linear map. -/
theorem map_linearIsometryEquiv (h : LocalConeGerm S x C)
    (L : E ≃ₗᵢ[ℝ] F) :
    LocalConeGerm (L '' S) (L x) (L '' C) :=
  h.map_continuousLinearEquiv L.toContinuousLinearEquiv

/-- Every real isometric equivalence transports a local body cone by its
Mazur-Ulam linear displacement map. Reflections and arbitrary mixing of
product coordinates are included. -/
theorem map_isometryEquiv (h : LocalConeGerm S x C) (f : E ≃ᵢ F) :
    LocalConeGerm (f '' S) (f x) (f.toRealLinearIsometryEquiv '' C) := by
  apply h.map_equiv_of_displacement f.toEquiv
    f.toRealLinearIsometryEquiv.toContinuousLinearEquiv
  intro p v
  have hadd := f.toRealLinearIsometryEquiv.map_add p v
  simp only [IsometryEquiv.toRealLinearIsometryEquiv_apply] at hadd
  change f (p + v) = f p + f.toRealLinearIsometryEquiv v
  rw [IsometryEquiv.toRealLinearIsometryEquiv_apply]
  calc
    f (p + v) = (f (p + v) - f 0) + f 0 := by abel
    _ = ((f p - f 0) + (f v - f 0)) + f 0 := by rw [hadd]
    _ = f p + (f v - f 0) := by abel

end LocalConeGerm
end
end SpectreGeometry
