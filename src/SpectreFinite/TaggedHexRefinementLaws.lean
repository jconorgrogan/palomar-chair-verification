module

public import SpectreFinite.TaggedHexPortFrames
public import SpectreFinite.TaggedHexBoundary
public import SpectreFinite.ForwardInternalPortLaws
public import SpectreFinite.ForwardSeamPortLaws

@[expose] public section


/-! Inverse-port and facing-mark preservation for the actual tagged
substitution, derived from finite internal and seam routing certificates. -/
namespace SpectreFinite.HexSearch.PartialMarkedHexSystem
open Boundary ForwardSubstitution

theorem forwardPort_of_external (k : TileKind) (i : Fin 8) (d s n : Fin 6)
    (hi : i.val < (children k).length) (h : portAction k i d = .external s n) :
    forwardPort k s n = (i,d) := by
  have hr := portAction_external_reference k i d s n hi h
  simp [forwardPort,List.getD_eq_getElem?_getD,hr,Nat.mod_eq_of_lt i.isLt]

theorem taggedStep_reverse_and_marks (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) (x y : ChildTag S) (he : S.taggedStep d x = some y) :
    S.taggedStep (opposite d) y = some x ∧
    facingMark (placed ((0,0),S.childLabel x)) d =
      -facingMark (placed ((0,0),S.childLabel y)) (opposite d) := by
  cases ha : portAction (S.label x.parent).1 (S.childFin8 x)
      (localDirection (S.label x.parent).2 d) with
  | internal j =>
      have hy : S.tagAt x.parent j = some y := by
        simpa only [taggedStep,ha] using he
      obtain ⟨hp,hi⟩ := (S.tagAt_eq_some_iff x.parent j y).mp hy
      have hr := internal_port_inverse _ _ j _ x.child.isLt ha
      constructor
      · unfold taggedStep
        dsimp only
        rw [hp,hi,localDirection_opposite,hr.1]
        exact S.tagAt_childFin8 x
      · rw [S.childLabel_mark x d,S.childLabel_mark y (opposite d),hp,hi,
          localDirection_opposite]
        exact hr.2
  | external s n =>
      cases hq : S.step (macroSide (S.label x.parent).2 s) x.parent with
      | none => simp [taggedStep,ha,hq] at he
      | some q =>
          let D := macroSide (S.label x.parent).2 s
          let t := macroSide (S.label q).2 (opposite D)
          let j := matingPort (S.label q).1 t n
          have hy : S.tagAt q j.1 = some y := by
            simpa only [taggedStep,ha,hq,Option.bind_some] using he
          obtain ⟨hp,hi⟩ := (S.tagAt_eq_some_iff q j.1 y).mp hy
          have hm := S.coarse_mating_marks hs x.parent q s hq
          have hn := portAction_external_slot_lt _ _ _ s n x.child.isLt ha
          have hl := (all_seam_port_laws _ _ s t hm).2 n hn
          rw [forwardPort_of_external _ _ _ s n x.child.isLt ha] at hl
          obtain ⟨_,_,_,hback,hmate,hdir,hmarks⟩ := hl
          have hd : j.2 = localDirection (S.label q).2 (opposite d) :=
            seam_localDirection (S.label x.parent).2 (S.label q).2 s d j.2 hdir
          have hD : macroSide (S.label q).2 t = opposite D := macroSide_involutive _ _
          have hreturn : macroSide (S.label x.parent).2 (opposite (opposite D)) = s := by
            rw [opposite_opposite_port]
            exact macroSide_involutive _ _
          have hqback := hs.opposite_inverse D x.parent q hq
          constructor
          · unfold taggedStep
            dsimp only
            rw [hp,hi,←hd,hback]
            dsimp only
            rw [hD,hqback]
            simp only [Option.bind_some]
            rw [hreturn,hmate]
            exact S.tagAt_childFin8 x
          · rw [S.childLabel_mark x d,S.childLabel_mark y (opposite d),hp,hi,←hd]
            exact hmarks

theorem taggedStep_inverse (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) (x y : ChildTag S) (he : S.taggedStep d x = some y) :
    S.taggedStep (opposite d) y = some x :=
  (S.taggedStep_reverse_and_marks hs d x y he).1

theorem taggedStep_matching (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) (x y : ChildTag S) (he : S.taggedStep d x = some y) :
    facingMark (placed ((0,0),S.childLabel x)) d =
      -facingMark (placed ((0,0),S.childLabel y)) (opposite d) :=
  (S.taggedStep_reverse_and_marks hs d x y he).2

theorem refine_opposite_inverse (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) (v w : S.refine.Cell) (he : S.refine.step d v = some w) :
    S.refine.step (opposite d) w = some v := by
  have hx : S.taggedStep d (S.decodeChild v) = some (S.decodeChild w) := by
    have h := congrArg (Option.map S.decodeChild) he
    change Option.map S.decodeChild
      (Option.map S.encodeChild (S.taggedStep d (S.decodeChild v))) =
        some (S.decodeChild w) at h
    simpa only [Option.map_map,Function.comp_def,decode_encodeChild,Option.map_id'] using h
  have hr := S.taggedStep_inverse hs d _ _ hx
  change (S.taggedStep (opposite d) (S.decodeChild w)).map S.encodeChild = some v
  rw [hr]
  change some (S.encodeChild (S.decodeChild v)) = some v
  rw [S.encode_decodeChild v]
  rfl

theorem refine_matching (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) (v w : S.refine.Cell) (he : S.refine.step d v = some w) :
    S.refine.mark v d = -S.refine.mark w (opposite d) := by
  have hx : S.taggedStep d (S.decodeChild v) = some (S.decodeChild w) := by
    have h := congrArg (Option.map S.decodeChild) he
    change Option.map S.decodeChild
      (Option.map S.encodeChild (S.taggedStep d (S.decodeChild v))) =
        some (S.decodeChild w) at h
    simpa only [Option.map_map,Function.comp_def,decode_encodeChild,Option.map_id'] using h
  exact S.taggedStep_matching hs d _ _ hx

end SpectreFinite.HexSearch.PartialMarkedHexSystem
