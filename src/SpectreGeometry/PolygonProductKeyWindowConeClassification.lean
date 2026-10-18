module

public import SpectreGeometry.PolygonProductKeyConeModels
public import SpectreGeometry.PolygonProductKeyIncidentNormals

@[expose] public section


/-! Actual window strata produce full closed finite-sign cone models. The
classification records the literal key and branch angle, so later recognition
can recover its absolute label rather than merely its numerical bounds. -/
namespace SpectreGeometry.ProductCrease
noncomputable section
open Set MeasureTheory FiniteConeFan
open scoped InnerProductSpace

/-- A literal nonflat key sector, retaining its actual key and branch. -/
def ActualKeyMass (f : EFour ≃ᵢ EFour) (x : EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (C : Set EFour) : Prop :=
  ∃ u : ProductKeySite, x ∈ f '' creaseComplex u ∧
    ((∃ b : ProductKeySide, coneAngularMass L C = baseMaterialAngle u b) ∨
     (∃ b c : ProductKeySide, b.1 ≠ c.1 ∧ coneAngularMass L C = sideMaterialAngle u b c))

/-- All ordinary mass is a positive integral multiple of π/6. -/
def ConeSectorClassification (f : EFour ≃ᵢ EFour) (x : EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (C : Set EFour) : Prop :=
  (∃ k : ℕ, 0 < k ∧ coneAngularMass L C = (k : ℝ) * (Real.pi/6)) ∨
    ActualKeyMass f x L C

theorem ActualKeyMass.bounds {f : EFour ≃ᵢ EFour} {x : EFour}
    {L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour} {C : Set EFour}
    (h : ActualKeyMass f x L C) :
    11*Real.pi/12 < coneAngularMass L C ∧
      coneAngularMass L C < 13*Real.pi/12 ∧ coneAngularMass L C ≠ Real.pi := by
  obtain ⟨u,_,h | h⟩ := h
  · obtain ⟨b,hb⟩ := h
    rw [hb]
    exact baseMaterialAngle_bounds u b
  · obtain ⟨b,c,hbc,he⟩ := h
    rw [he]
    exact sideMaterialAngle_bounds u b c hbc

private theorem classification_of_flat {f : EFour ≃ᵢ EFour} {x : EFour}
    {L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour} {C : Set EFour}
    (h : coneAngularMass L C = Real.pi) : ConeSectorClassification f x L C := by
  left
  refine ⟨6,by decide,?_⟩
  rw [h]
  norm_num
  ring

/-- Pointwise actual classification when all its passing boundary normals
are known to lie in the given transverse chart. -/
theorem key_window_cone_model (f : EFour ≃ᵢ EFour) (x : EFour)
    (L : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EFour) (u : ProductKeySite)
    (hx : f.symm x ∈ productKeyGraphWindow u)
    (hs : KeyWindowStratum u (f.symm x))
    (hr : ∀ b : ProductKeyBoundaryPlaneIndex,
      x ∈ f '' productKeyBoundaryPlane b →
      f.toRealLinearIsometryEquiv (productKeyBoundaryPlaneNormal b) ∈ Set.range L) :
    ∃ M : ActualBoundaryConeModel f x L, ConeSectorClassification f x L M.cone := by
  have ho (hz : inner ℝ (productKeyOutwardNormal u) (f.symm x-productKeyCenter u) = 0) :
      f.toRealLinearIsometryEquiv (productKeyOutwardNormal u) ∈ Set.range L :=
    hr (.inr (u,none)) ⟨f.symm x,hz,f.apply_symm_apply x⟩
  have hb (b : ProductKeySide) (hy : f.symm x ∈ productKeySideFace u b) :
      f.toRealLinearIsometryEquiv (productKeySideNormal u b) ∈ Set.range L :=
    hr (.inr (u,some b)) ⟨f.symm x,product_key_side_face_plane u b _ hy,f.apply_symm_apply x⟩
  rcases hs with ⟨b,hneg⟩ | ⟨b,hstrict⟩ | ⟨b,hbase⟩ | ⟨b,c,hbc,hside⟩
  · have hz := hx.1.trans (product_key_height_zero_of_nonpos_branch u b (f.symm x) hneg.le)
    have hn := product_key_boundary_plane_normal_ne_zero (.inr (u,none))
    obtain ⟨M,hM⟩ := exists_flat_boundary_cone_model f (f.symm x) (productKeyOutwardNormal u)
      L hn (ho hz) (product_key_negative_branch_local_cone u b (f.symm x) hx hneg)
    have hclass : ConeSectorClassification f (f (f.symm x)) L M.cone := classification_of_flat hM
    have hh : ∃ M : ActualBoundaryConeModel f (f (f.symm x)) L,
        ConeSectorClassification f (f (f.symm x)) L M.cone := ⟨M,hclass⟩
    rw [f.apply_symm_apply] at hh
    exact hh
  · have hface : f.symm x ∈ productKeySideFace u b :=
      ⟨hx.1,hstrict.1.le,fun c => by
        by_cases he : c = b
        · rw [he]
        · exact (hstrict.2 ⟨c,he⟩).le⟩
    have hn := product_key_boundary_plane_normal_ne_zero (.inr (u,some b))
    obtain ⟨M,hM⟩ := exists_flat_boundary_cone_model f (f.symm x) (productKeySideNormal u b)
      L hn (hb b hface) (product_key_strict_branch_local_cone u b (f.symm x) hx hstrict.1 (fun c hc => hstrict.2 ⟨c,hc⟩))
    have hclass : ConeSectorClassification f (f (f.symm x)) L M.cone := classification_of_flat hM
    have hh : ∃ M : ActualBoundaryConeModel f (f (f.symm x)) L,
        ConeSectorClassification f (f (f.symm x)) L M.cone := ⟨M,hclass⟩
    rw [f.apply_symm_apply] at hh
    exact hh
  · obtain ⟨M,hM,hcrease⟩ := exists_base_boundary_cone_model f (f.symm x) L u b hbase
      (ho hbase.1.2) (hb b hbase.1.1)
    have hclass : ConeSectorClassification f (f (f.symm x)) L M.cone :=
      Or.inr ⟨u,hcrease,Or.inl ⟨b,hM⟩⟩
    have hh : ∃ M : ActualBoundaryConeModel f (f (f.symm x)) L,
        ConeSectorClassification f (f (f.symm x)) L M.cone := ⟨M,hclass⟩
    rw [f.apply_symm_apply] at hh
    exact hh
  · obtain ⟨M,hM,hcrease⟩ := exists_side_boundary_cone_model f (f.symm x) L u b c hbc hside
      (hb b hside.1.1) (hb c hside.1.2)
    have hclass : ConeSectorClassification f (f (f.symm x)) L M.cone :=
      Or.inr ⟨u,hcrease,Or.inr ⟨b,c,hbc,hM⟩⟩
    have hh : ∃ M : ActualBoundaryConeModel f (f (f.symm x)) L,
        ConeSectorClassification f (f (f.symm x)) L M.cone := ⟨M,hclass⟩
    rw [f.apply_symm_apply] at hh
    exact hh

end
end SpectreGeometry.ProductCrease
