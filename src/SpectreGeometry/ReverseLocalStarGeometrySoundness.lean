module

public import SpectreGeometry.ReverseLocalStarGeometryData
public import SpectreGeometry.ReverseLocalStarCanonicalBinding
public import SpectreGeometry.ReverseLocalStarRotation

@[expose] public section


namespace SpectreGeometry.ReverseLocalStarOccurrences
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch

private theorem kind_flag (k : Fin 9) :
    (k.val != 0) = (if k.val=0 then false else true) := by
  fin_cases k <;> rfl

private theorem getD_take_lt {α : Type*} (l : List α) (i n : Nat) (a : α) (hi : i<n) :
    (l.take n).getD i a = l.getD i a := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_take_of_lt hi]

theorem sideGeometryStar_take (g : List Nat) : sideGeometryStar (g.take 5) = sideGeometryStar g := by
  simp only [sideGeometryStar,getD_take_lt g 0 5 0 (by decide),getD_take_lt g 1 5 0 (by decide),
    getD_take_lt g 2 5 0 (by decide),getD_take_lt g 3 5 0 (by decide),getD_take_lt g 4 5 0 (by decide)]

theorem tripleGeometryStar_take (g : List Nat) : tripleGeometryStar (g.take 8) = tripleGeometryStar g := by
  simp only [tripleGeometryStar,sideGeometryStar,getD_take_lt g 0 8 0 (by decide),
    getD_take_lt g 1 8 0 (by decide),getD_take_lt g 2 8 0 (by decide),getD_take_lt g 3 8 0 (by decide),
    getD_take_lt g 4 8 0 (by decide),getD_take_lt g 5 8 0 (by decide),getD_take_lt g 6 8 0 (by decide),
    getD_take_lt g 7 8 0 (by decide)]

theorem sideGeometryStar_key (k : Fin 9) (b : State) (d : Fin 6) (j : Nat) :
    sideGeometryStar (sideGeometryKey (k,0) b d j) =
      fastLocalStar (k,0) ((stateBoundaryIds (k,0) d).getD j 0) ++
      fastLocalStar b ((stateBoundaryIds b (opposite d)).getD
        ((stateBoundaryIds b (opposite d)).length-1-j) 0) := by
  rcases b with ⟨bk,br⟩
  by_cases hk : k.val=0 <;> by_cases hb : bk.val=0 <;>
    simp [sideGeometryStar,sideGeometryKey,rawGeometryState,fastLocalStar,kind_flag,hk,hb,
      Nat.mod_eq_of_lt br.isLt]

theorem tripleGeometryStar_key (k : Fin 9) (b c : State) (d : Fin 6) :
    tripleGeometryStar (tripleGeometryKey (k,0) b c d) =
      fastLocalStar (k,0) ((stateBoundaryIds (k,0) d).getLastD 0) ++
      fastLocalStar b ((stateBoundaryIds b (opposite d)).headD 0) ++
      fastLocalStar c ((stateBoundaryIds c (rotateTurn 4 (rotateTurn 1 d))).headD 0) := by
  rcases b with ⟨bk,br⟩
  rcases c with ⟨ck,cr⟩
  by_cases hk : k.val=0 <;> by_cases hb : bk.val=0 <;> by_cases hc : ck.val=0 <;>
    simp [tripleGeometryStar,sideGeometryStar,tripleGeometryKey,rawGeometryState,fastLocalStar,
      kind_flag,hk,hb,hc,Nat.mod_eq_of_lt br.isLt,Nat.mod_eq_of_lt cr.isLt]

theorem structural_occurrence_origin (ts : List (List Point)) (code : Nat)
    (hc : occurrenceStructuralB ts code = true) :
    (0:RealPoint) ∈ interior (starBody ts) := by
  have hb := (occurrenceStructuralB_sound ts code hc).1
  have hlt : code/6 < 124 := by omega
  exact structural_occurrence_origin_interior ts code hc (canonicalStar_origin_interior ⟨code/6,hlt⟩)

theorem sideGeometry_origin_interior (i : Fin 217) (h : SideGeometryCertificate i.val) :
    (0:RealPoint) ∈ interior (starBody (sideGeometryStar (sideGeometryValues.getD i.val []))) :=
  structural_occurrence_origin _ _ h

theorem tripleGeometry_origin_interior (i : Fin 49) (h : TripleGeometryCertificate i.val) :
    (0:RealPoint) ∈ interior (starBody (tripleGeometryStar (tripleGeometryValues.getD i.val []))) :=
  structural_occurrence_origin _ _ h

end
end SpectreGeometry.ReverseLocalStarOccurrences
