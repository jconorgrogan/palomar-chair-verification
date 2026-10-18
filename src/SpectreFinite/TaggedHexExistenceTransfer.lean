module

public import SpectreFinite.TaggedHexRefinementLaws
public import SpectreFinite.TaggedHexTriangleTransfer
public import SpectreFinite.PartialHexFieldExistence

@[expose] public section


/-! Finite-rule transfer to actual iterated systems and the marked-field
compactness endpoint. The literal finite certificates are supplied separately. -/
namespace SpectreFinite.HexSearch.PartialMarkedHexSystem
open Boundary ForwardSubstitution

theorem refine_triangle_from_port_laws
    (hpairs : ∀ k l : TileKind, ∀ s t : Fin 6, PairPortTriangleCertificate k l s t)
    (htriples : ∀ k : TileKind, ∀ s : Fin 6, RootPortTriangleCertificate k s)
    (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) (v w z : S.refine.Cell)
    (hw : S.refine.step d v = some w)
    (hz : S.refine.step (rotateTurn 1 d) v = some z) :
    S.refine.step (rotateTurn 2 d) w = some z := by
  have hw' : S.taggedStep d (S.decodeChild v) = some (S.decodeChild w) := by
    have h := congrArg (Option.map S.decodeChild) hw
    change Option.map S.decodeChild
      (Option.map S.encodeChild (S.taggedStep d (S.decodeChild v))) =
        some (S.decodeChild w) at h
    simpa only [Option.map_map,Function.comp_def,decode_encodeChild,Option.map_id'] using h
  have hz' : S.taggedStep (rotateTurn 1 d) (S.decodeChild v) = some (S.decodeChild z) := by
    have h := congrArg (Option.map S.decodeChild) hz
    change Option.map S.decodeChild
      (Option.map S.encodeChild (S.taggedStep (rotateTurn 1 d) (S.decodeChild v))) =
        some (S.decodeChild z) at h
    simpa only [Option.map_map,Function.comp_def,decode_encodeChild,Option.map_id'] using h
  have ht := taggedStep_triangle_of_port_laws hpairs htriples S hs d _ _ _ hw' hz'
  change (S.taggedStep (rotateTurn 2 d) (S.decodeChild w)).map S.encodeChild = some z
  rw [ht]
  change some (S.encodeChild (S.decodeChild z)) = some z
  rw [S.encode_decodeChild z]
  rfl

theorem refine_wellFormed_from_port_laws
    (hpairs : ∀ k l : TileKind, ∀ s t : Fin 6, PairPortTriangleCertificate k l s t)
    (htriples : ∀ k : TileKind, ∀ s : Fin 6, RootPortTriangleCertificate k s)
    (S : PartialMarkedHexSystem) (hs : S.WellFormed) :
    S.refine.WellFormed where
  opposite_inverse := S.refine_opposite_inverse hs
  matching := S.refine_matching hs
  triangle := refine_triangle_from_port_laws hpairs htriples S hs

theorem iterateRefinement_wellFormed_from_port_laws
    (hpairs : ∀ k l : TileKind, ∀ s t : Fin 6, PairPortTriangleCertificate k l s t)
    (htriples : ∀ k : TileKind, ∀ s : Fin 6, RootPortTriangleCertificate k s)
    (s : State) (n : Nat) :
    (iterateRefinement s n).WellFormed := by
  induction n with
  | zero => exact singleton_wellFormed s
  | succ n ih => exact refine_wellFormed_from_port_laws hpairs htriples _ ih

theorem iterateRefinement_boundary_from_port_laws
    (hpairs : ∀ k l : TileKind, ∀ s t : Fin 6, PairPortTriangleCertificate k l s t)
    (htriples : ∀ k : TileKind, ∀ s : Fin 6, RootPortTriangleCertificate k s)
    (s : State) (n : Nat) :
    (iterateRefinement s n).boundaryPorts.length ≤ 6*6^n := by
  induction n with
  | zero => simp only [iterateRefinement,singleton_boundary_length,Nat.pow_zero,Nat.mul_one,Nat.le_refl]
  | succ n ih =>
      have h := (iterateRefinement s n).refine_boundaryCount_le_six
        (iterateRefinement_wellFormed_from_port_laws hpairs htriples s n)
      change (iterateRefinement s n).refine.boundaryPorts.length ≤ 6*6^(n+1)
      calc
        (iterateRefinement s n).refine.boundaryPorts.length ≤
            (iterateRefinement s n).boundaryPorts.length*6 := h
        _ ≤ (6*6^n)*6 := Nat.mul_le_mul_right 6 ih
        _ = 6*6^(n+1) := by rw [Nat.pow_succ,Nat.mul_assoc]

/-- Explicit finite pair/triple routing laws suffice for the actual literal
iteration to give a discrete globally legal marked field. -/
theorem exists_globallyLegal_from_port_laws
    (hpairs : ∀ k l : TileKind, ∀ s t : Fin 6, PairPortTriangleCertificate k l s t)
    (htriples : ∀ k : TileKind, ∀ s : Fin 6, RootPortTriangleCertificate k s) :
    ∃ f : Position → State, GloballyLegal f :=
  exists_globallyLegal_of_growing_systems (iterateRefinement (0,0)) 6
    (iterateRefinement_wellFormed_from_port_laws hpairs htriples (0,0)) (iterateRefinement_area (0,0))
    (iterateRefinement_boundary_from_port_laws hpairs htriples (0,0))

end SpectreFinite.HexSearch.PartialMarkedHexSystem
