module

public import SpectreGeometry.ReverseLocalStarGeometrySoundness

@[expose] public section


namespace SpectreGeometry.ReverseLocalStarOccurrences
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch

/-- The exact two incident stars, in the common raw frame at a matching
boundary subdivision vertex. -/
def sideStarList (a b : State) (d : Fin 6) (j : Nat) : List (List Point) :=
  fastLocalStar a ((stateBoundaryIds a d).getD j 0) ++
  fastLocalStar b ((stateBoundaryIds b (opposite d)).getD
    ((stateBoundaryIds b (opposite d)).length-1-j) 0)

/-- The exact three incident stars at the terminal corner of side d. -/
def tripleStarList (a b c : State) (d : Fin 6) : List (List Point) :=
  fastLocalStar a ((stateBoundaryIds a d).getLastD 0) ++
  fastLocalStar b ((stateBoundaryIds b (opposite d)).headD 0) ++
  fastLocalStar c ((stateBoundaryIds c (rotateTurn 4 (rotateTurn 1 d))).headD 0)

theorem normalized_side_origin
    (hcert : ∀ i : Fin 217, SideGeometryCertificate i.val)
    (hbind : ∀ k d, SideGeometryBinding k d)
    (k : Fin 9) (b : State) (d : Fin 6) (j : Fin 12)
    (hm : sideMatch (k,0) b d) (hj : 0<j.val)
    (hj' : j.val+1<(stateBoundaryIds (k,0) d).length) :
    (0:RealPoint) ∈ interior (starBody (sideStarList (k,0) b d j.val)) := by
  obtain ⟨hc,hkey⟩ := hbind k d b.1 b.2 j hm hj hj'
  have h := sideGeometry_origin_interior ⟨sideGeometryCode (k,0) b d j.val,hc⟩
    (hcert ⟨_,hc⟩)
  rw [←sideGeometryStar_take,hkey,sideGeometryStar_key] at h
  exact h

theorem normalized_triple_origin
    (hcert : ∀ i : Fin 49, TripleGeometryCertificate i.val)
    (hbind : ∀ k d, TripleGeometryBinding k d)
    (k : Fin 9) (b c : State) (d : Fin 6)
    (hab : sideMatch (k,0) b d)
    (hac : sideMatch (k,0) c (rotateTurn 1 d))
    (hbc : sideMatch b c (rotateTurn 2 d)) :
    (0:RealPoint) ∈ interior (starBody (tripleStarList (k,0) b c d)) := by
  obtain ⟨hc,hkey⟩ := hbind k d b.1 b.2 c.1 c.2 hab hac hbc
  have h := tripleGeometry_origin_interior ⟨tripleGeometryCode (k,0) b c d,hc⟩
    (hcert ⟨_,hc⟩)
  rw [←tripleGeometryStar_take,hkey,tripleGeometryStar_key] at h
  exact h

private theorem turn_commutes : ∀ r s d : Fin 6,
    rotateTurn r (rotateTurn s d) = rotateTurn s (rotateTurn r d) := by decide

theorem sideStarList_rotate (r : Fin 6) (a b : State) (d : Fin 6) (j : Nat) :
    sideStarList (rotateState r a) (rotateState r b) (rotateTurn r d) j =
      rotatedStar (sideStarList a b d j) r := by
  simp only [sideStarList,←rotateTurn_opposite,stateBoundaryIds_rotate,fastLocalStar_rotate,
    rotatedStar,List.map_append]

theorem tripleStarList_rotate (r : Fin 6) (a b c : State) (d : Fin 6) :
    tripleStarList (rotateState r a) (rotateState r b) (rotateState r c) (rotateTurn r d) =
      rotatedStar (tripleStarList a b c d) r := by
  have he : rotateTurn 4 (rotateTurn 1 (rotateTurn r d)) =
      rotateTurn r (rotateTurn 4 (rotateTurn 1 d)) := by
    rw [turn_commutes 1 r,turn_commutes 4 r]
  simp only [tripleStarList,←rotateTurn_opposite,he,stateBoundaryIds_rotate,fastLocalStar_rotate,
    rotatedStar,List.map_append]

theorem origin_interior_of_rotated (ts : List (List Point)) (r : Fin 6)
    (h : (0:RealPoint) ∈ interior (starBody (rotatedStar ts r))) :
    (0:RealPoint) ∈ interior (starBody ts) := by
  rw [starBody_rotate,←(gridTurnHomeomorph r).image_interior] at h
  obtain ⟨x,hx,hzero⟩ := h
  have hz : gridTurnHomeomorph r 0 = 0 := (gridRotationLinear r).map_zero
  have hx0 : x=0 := (gridTurnHomeomorph r).injective (hzero.trans hz.symm)
  simpa only [hx0] using hx

theorem side_origin
    (hcert : ∀ i : Fin 217, SideGeometryCertificate i.val)
    (hbind : ∀ k d, SideGeometryBinding k d)
    (a b : State) (d : Fin 6) (j : Fin 12)
    (hm : sideMatch a b d) (hj : 0<j.val)
    (hj' : j.val+1<(stateBoundaryIds a d).length) :
    (0:RealPoint) ∈ interior (starBody (sideStarList a b d j.val)) := by
  let r := inverseTurn a.2
  have hm' := sideMatch_rotate r a b d hm
  have hid := stateBoundaryIds_rotate r a d
  rw [state_normalized a] at hm' hid
  have hh := normalized_side_origin hcert hbind a.1 (rotateState r b) (rotateTurn r d)
    j hm' hj (by simpa only [hid] using hj')
  rw [←state_normalized a,sideStarList_rotate] at hh
  exact origin_interior_of_rotated _ r hh

theorem triple_origin
    (hcert : ∀ i : Fin 49, TripleGeometryCertificate i.val)
    (hbind : ∀ k d, TripleGeometryBinding k d)
    (a b c : State) (d : Fin 6)
    (hab : sideMatch a b d)
    (hac : sideMatch a c (rotateTurn 1 d))
    (hbc : sideMatch b c (rotateTurn 2 d)) :
    (0:RealPoint) ∈ interior (starBody (tripleStarList a b c d)) := by
  let r := inverseTurn a.2
  have hab' := sideMatch_rotate r a b d hab
  have hac' := sideMatch_rotate r a c (rotateTurn 1 d) hac
  have hbc' := sideMatch_rotate r b c (rotateTurn 2 d) hbc
  rw [state_normalized a] at hab' hac'
  rw [turn_commutes r 1] at hac'
  rw [turn_commutes r 2] at hbc'
  have hh := normalized_triple_origin hcert hbind a.1 (rotateState r b) (rotateState r c)
    (rotateTurn r d) hab' hac' hbc'
  rw [←state_normalized a,tripleStarList_rotate] at hh
  exact origin_interior_of_rotated _ r hh

end
end SpectreGeometry.ReverseLocalStarOccurrences
