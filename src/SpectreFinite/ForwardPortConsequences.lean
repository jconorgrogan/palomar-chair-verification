module

public import SpectreFinite.ForwardPortActions

@[expose] public section


namespace SpectreFinite.HexSearch.ForwardSubstitution
open Boundary

theorem portAction_internal_bound (k : TileKind) (i j : Fin 8) (d : Fin 6)
    (hi : i.val < (children k).length) (h : portAction k i d = .internal j) :
    j.val < (children k).length := by
  have hvalid := (all_port_actions k).1 i hi d
  rw [h] at hvalid
  exact hvalid.1

theorem portAction_external_reference (k : TileKind) (i : Fin 8) (d s n : Fin 6)
    (hi : i.val < (children k).length) (h : portAction k i d = .external s n) :
    (segment k s)[n.val]? = some ⟨i.val,d⟩ := by
  have hvalid := (all_port_actions k).1 i hi d
  rw [h] at hvalid
  exact hvalid

theorem portAction_external_slot_lt (k : TileKind) (i : Fin 8) (d s n : Fin 6)
    (hi : i.val < (children k).length) (h : portAction k i d = .external s n) :
    n.val < (segment k s).length :=
  ((List.getElem?_eq_some_iff).mp (portAction_external_reference k i d s n hi h)).1

theorem portAction_external_injective (k : TileKind) (i j : Fin 8) (d e s n : Fin 6)
    (hi : i.val < (children k).length) (hj : j.val < (children k).length)
    (h : portAction k i d = .external s n) (h' : portAction k j e = .external s n) :
    i = j ∧ d = e := by
  have hi' := portAction_external_reference k i d s n hi h
  have hj' := portAction_external_reference k j e s n hj h'
  have heq := Option.some.inj (hi'.symm.trans hj')
  exact ⟨Fin.ext (congrArg SideRef.child heq), congrArg SideRef.side heq⟩

theorem complementary_segment_lengths (k l : TileKind) (s t : Fin 6)
    (hm : macroLabel k s = -macroLabel l t) :
    (segment k s).length = (segment l t).length := by
  have h := all_forward_seams k l s t hm
  have hlen := congrArg List.length h
  simpa only [ParentBoundary.placedSegment, ParentBoundary.matingSegment,
    List.length_map, List.length_reverse] using hlen.symm

theorem matingPort_bound (k l : TileKind) (s t n : Fin 6)
    (hm : macroLabel k s = -macroLabel l t) (hn : n.val < (segment k s).length) :
    (matingPort l t n).1.val < (children l).length := by
  have hlen := complementary_segment_lengths k l s t hm
  exact (all_port_actions l).2.2 t n (by omega)

end SpectreFinite.HexSearch.ForwardSubstitution
