module

public import SpectreGeometry.ReverseLocalStarOccurrenceSoundness
public import SpectreGeometry.ReverseFinitePLScaling
public import SpectreGeometry.ReverseSourceHexRotation

@[expose] public section


/-! Exact carrier transport for the local-star occurrence certificates. -/
namespace SpectreGeometry.ReverseLocalStarOccurrences
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation ReverseFinitePL ReverseExistence
open SpectreFinite.HexSearch

def gridTurnHomeomorph (r : Fin 6) : RealPoint ≃ₜ RealPoint where
  toFun := gridRotation r
  invFun := gridRotation (inverseTurn r)
  left_inv p := by
    have h := gridRotation_inverse_cancel (inverseTurn r) p
    simpa only [inverseTurn_involutive] using h
  right_inv := gridRotation_inverse_cancel r
  continuous_toFun := (gridRotationLinear r).continuous_of_finiteDimensional
  continuous_invFun := (gridRotationLinear (inverseTurn r)).continuous_of_finiteDimensional

theorem starBody_vertices (ps : List PolygonPacket) :
    starBody (ps.map PolygonPacket.vertices) = familyBody ps := by
  ext x
  simp only [starBody,familyBody,mem_ofPred_eq,List.mem_map,mem_iUnion]
  constructor
  · rintro ⟨vs,⟨p,hp,rfl⟩,hx⟩
    exact ⟨p,hp,hx⟩
  · rintro ⟨p,hp,hx⟩
    exact ⟨p.vertices,⟨p,hp,rfl⟩,hx⟩

theorem starBody_scale (n : Int) (ts : List (List Point)) :
    starBody (ts.map (fun t => t.map (scalePoint n))) =
      (fun x : RealPoint => (n:ℝ) • x) '' starBody ts := by
  ext x
  constructor
  · rintro ⟨u,hu,hx⟩
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hu
    rw [integerHull_scale] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨y,⟨t,ht,hy⟩,rfl⟩
  · rintro ⟨y,⟨t,ht,hy⟩,rfl⟩
    refine ⟨t.map (scalePoint n),List.mem_map.mpr ⟨t,ht,rfl⟩,?_⟩
    rw [integerHull_scale]
    exact ⟨y,hy,rfl⟩

theorem integerHull_rotate (r : Fin 6) (vs : List Point) :
    integerHull (vs.map (SpectreClusters.rotate r)) = gridRotation r '' integerHull vs := by
  have h := integerHull_image_motion r (0,0) vs
  have hh : integerHull (vs.map (SpectreClusters.rotate r)) =
      (fun a : RealPoint => (0,0)+gridRotation r a) '' integerHull vs := by
    simpa [lattice,SpectreClusters.add,integerPoint,gridMotion_apply] using h
  have he : (fun a : RealPoint => (0,0)+gridRotation r a) = gridRotation r := by
    funext a
    exact _root_.zero_add _
  simpa only [he] using hh

theorem starBody_rotate (r : Fin 6) (ts : List (List Point)) :
    starBody (rotatedStar ts r) = gridTurnHomeomorph r '' starBody ts := by
  ext x
  constructor
  · rintro ⟨u,hu,hx⟩
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hu
    rw [integerHull_rotate] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨y,⟨t,ht,hy⟩,rfl⟩
  · rintro ⟨y,⟨t,ht,hy⟩,rfl⟩
    refine ⟨t.map (SpectreClusters.rotate r),List.mem_map.mpr ⟨t,ht,rfl⟩,?_⟩
    rw [integerHull_rotate]
    exact ⟨y,hy,rfl⟩

/-- The finite 1000-times scaled box-cover certificate supplies an actual
ambient neighborhood in the unscaled canonical star. -/
theorem origin_interior_of_scaled_packets (ps : List PolygonPacket) (ts : List (List Point))
    (hbind : normalized (ps.map PolygonPacket.vertices) =
      normalized (ts.map (fun t => t.map (scalePoint 1000))))
    (h : (0:RealPoint) ∈ interior (familyBody ps)) :
    (0:RealPoint) ∈ interior (starBody ts) := by
  have he : familyBody ps = (scalarHomeomorph 1000 (by norm_num)) '' starBody ts := by
    rw [←starBody_vertices,←starBody_normalized,hbind,starBody_normalized,starBody_scale]
    rfl
  rw [he,←(scalarHomeomorph 1000 (by norm_num)).image_interior] at h
  obtain ⟨x,hx,hzero⟩ := h
  have hx0 : x=0 := (scalarHomeomorph 1000 (by norm_num)).injective (by simpa using hzero)
  simpa only [hx0] using hx

/-- A checked occurrence inherits the canonical star's ambient neighborhood. -/
theorem occurrence_origin_interior (ts : List (List Point)) (code : Nat)
    (hc : occurrenceCheckB ts code = true)
    (h : (0:RealPoint) ∈ interior (starBody (canonicalStars.getD (code/6) []))) :
    (0:RealPoint) ∈ interior (starBody ts) := by
  have he := (occurrenceCheckB_sound ts code hc).2
  rw [←he,starBody_rotate,←(gridTurnHomeomorph _).image_interior] at h
  obtain ⟨x,hx,hzero⟩ := h
  have hz : gridTurnHomeomorph ⟨code%6,Nat.mod_lt _ (by decide)⟩ 0=0 := by
    change gridRotation _ 0=0
    exact (gridRotationLinear _).map_zero
  have hx0 : x=0 := (gridTurnHomeomorph _).injective (hzero.trans hz.symm)
  simpa only [hx0] using hx

end
end SpectreGeometry.ReverseLocalStarOccurrences
