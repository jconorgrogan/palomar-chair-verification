module

public import SpectreGeometry.ReverseLocalStarStructuralChecks
public import SpectreGeometry.ReverseLocalStarTransforms

@[expose] public section


namespace SpectreGeometry.ReverseLocalStarOccurrences
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation

theorem insertB_perm {α : Type} (le : α → α → Bool) (a : α) (l : List α) :
    (insertB le a l).Perm (a::l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons b l ih =>
    simp only [insertB]
    split
    · exact List.Perm.refl _
    · exact (ih.cons b).trans (List.Perm.swap b a l).symm

theorem sortB_perm {α : Type} (le : α → α → Bool) (l : List α) : (sortB le l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih => exact (insertB_perm le a _).trans (ih.cons a)

theorem starBody_normalizedStructural (ts : List (List Point)) :
    starBody (normalizedStructural ts) = starBody ts := by
  rw [normalizedStructural,starBody_perm (sortB_perm _ _)]
  ext x
  constructor
  · rintro ⟨t,ht,hx⟩
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    exact ⟨u,hu,(integerHull_perm (sortB_perm pointLE u)) ▸ hx⟩
  · rintro ⟨t,ht,hx⟩
    exact ⟨sortB pointLE t,List.mem_map.mpr ⟨t,ht,rfl⟩,
      (integerHull_perm (sortB_perm pointLE t)).symm ▸ hx⟩

theorem occurrenceStructuralB_sound (ts : List (List Point)) (code : Nat)
    (hc : occurrenceStructuralB ts code = true) :
    code<744 ∧ starBody (rotatedStar ts ⟨code%6,Nat.mod_lt _ (by decide)⟩) =
      starBody (canonicalStars.getD (code/6) []) := by
  have hh : code<744 ∧
      normalizedStructural (rotatedStar ts ⟨code%6,Nat.mod_lt _ (by decide)⟩) =
        normalizedStructural (canonicalStars.getD (code/6) []) := by
    simpa only [occurrenceStructuralB,rotatedStar,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using hc
  refine ⟨hh.1,?_⟩
  rw [←starBody_normalizedStructural (rotatedStar ts _),hh.2,starBody_normalizedStructural]

theorem structural_origin_interior_of_scaled_packets (ps : List PolygonPacket) (ts : List (List Point))
    (hbind : normalizedStructural (ps.map PolygonPacket.vertices) =
      normalizedStructural (ts.map (fun t => t.map (scalePoint 1000))))
    (h : (0:RealPoint) ∈ interior (familyBody ps)) :
    (0:RealPoint) ∈ interior (starBody ts) := by
  have he : familyBody ps = (ReverseFinitePL.scalarHomeomorph 1000 (by norm_num)) '' starBody ts := by
    rw [←starBody_vertices,←starBody_normalizedStructural,hbind,starBody_normalizedStructural,starBody_scale]
    rfl
  rw [he,←(ReverseFinitePL.scalarHomeomorph 1000 (by norm_num)).image_interior] at h
  obtain ⟨x,hx,hzero⟩ := h
  have hx0 : x=0 := (ReverseFinitePL.scalarHomeomorph 1000 (by norm_num)).injective (by simpa using hzero)
  simpa only [hx0] using hx

theorem structural_occurrence_origin_interior (ts : List (List Point)) (code : Nat)
    (hc : occurrenceStructuralB ts code = true)
    (h : (0:RealPoint) ∈ interior (starBody (canonicalStars.getD (code/6) []))) :
    (0:RealPoint) ∈ interior (starBody ts) := by
  have he := (occurrenceStructuralB_sound ts code hc).2
  rw [←he,starBody_rotate,←(gridTurnHomeomorph _).image_interior] at h
  obtain ⟨x,hx,hzero⟩ := h
  have hz : gridTurnHomeomorph ⟨code%6,Nat.mod_lt _ (by decide)⟩ 0=0 := by
    change gridRotation _ 0=0
    exact (gridRotationLinear _).map_zero
  have hx0 : x=0 := (gridTurnHomeomorph _).injective (hzero.trans hz.symm)
  simpa only [hx0] using hx

end
end SpectreGeometry.ReverseLocalStarOccurrences
