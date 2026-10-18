module

public import SpectreFinite.TaggedHexTriangleFrames
public import SpectreFinite.TaggedHexBoundary
public import SpectreFinite.ForwardInternalPortLaws
public import SpectreFinite.ForwardCornerPortLaws

@[expose] public section


/-! Generic consumption of the explicit finite native pair/triple port laws.
These finite hypotheses are discharged separately by literal-table proofs. -/
namespace SpectreFinite.HexSearch.PartialMarkedHexSystem
open Boundary ForwardSubstitution

theorem taggedStep_internal_end (S : PartialMarkedHexSystem) (x y : ChildTag S)
    (d : Fin 6) (j : Fin 8)
    (ha : portAction (S.label x.parent).1 (S.childFin8 x)
      (localDirection (S.label x.parent).2 d) = .internal j)
    (h : S.taggedStep d x = some y) :
    y.parent = x.parent ∧ S.childFin8 y = j := by
  have h' : S.tagAt x.parent j = some y := by simpa only [taggedStep,ha] using h
  exact (S.tagAt_eq_some_iff _ _ _).mp h'

theorem taggedStep_external_end (S : PartialMarkedHexSystem) (x y : ChildTag S)
    (d s n : Fin 6)
    (ha : portAction (S.label x.parent).1 (S.childFin8 x)
      (localDirection (S.label x.parent).2 d) = .external s n)
    (h : S.taggedStep d x = some y) :
    ∃ q : S.Cell,
      S.step (macroSide (S.label x.parent).2 s) x.parent = some q ∧
      y.parent = q ∧ S.childFin8 y =
        (matingPort (S.label q).1
          (macroSide (S.label q).2 (opposite (macroSide (S.label x.parent).2 s))) n).1 := by
  cases hq : S.step (macroSide (S.label x.parent).2 s) x.parent with
  | none => simp [taggedStep,ha,hq] at h
  | some q =>
      refine ⟨q,rfl,?_⟩
      apply (S.tagAt_eq_some_iff _ _ _).mp
      simpa only [taggedStep,ha,hq,Option.bind_some] using h

theorem taggedStep_triangle_of_port_laws
    (hpairs : ∀ k l : TileKind, ∀ s t : Fin 6, PairPortTriangleCertificate k l s t)
    (htriples : ∀ k : TileKind, ∀ s : Fin 6, RootPortTriangleCertificate k s)
    (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (d : Fin 6) (x y z : ChildTag S)
    (hy : S.taggedStep d x = some y)
    (hz : S.taggedStep (rotateTurn 1 d) x = some z) :
    S.taggedStep (rotateTurn 2 d) y = some z := by
  cases ha : portAction (S.label x.parent).1 (S.childFin8 x)
      (localDirection (S.label x.parent).2 d) with
  | internal j =>
      obtain ⟨hyp,hyi⟩ := S.taggedStep_internal_end x y d j ha hy
      cases hb : portAction (S.label x.parent).1 (S.childFin8 x)
          (localDirection (S.label x.parent).2 (rotateTurn 1 d)) with
      | internal h =>
          obtain ⟨hzp,hzi⟩ := S.taggedStep_internal_end x z _ h hb hz
          have hb' : portAction (S.label x.parent).1 (S.childFin8 x)
              (rotateTurn 1 (localDirection (S.label x.parent).2 d)) = .internal h := by
            simpa only [localDirection_rotate] using hb
          have ht := internal_port_triangle _ _ j h _ x.child.isLt ha hb'
          apply S.taggedStep_internal_eq y z (rotateTurn 2 d) h
          · simpa only [hyp,hyi,localDirection_rotate] using ht
          · exact hzp.trans hyp.symm
          · exact hzi
      | external s n =>
          obtain ⟨q,hq,hzp,hzi⟩ := S.taggedStep_external_end x z _ s n hb hz
          let t := macroSide (S.label q).2 (opposite (macroSide (S.label x.parent).2 s))
          have hm := S.coarse_mating_marks hs x.parent q s hq
          have ht := hpairs _ _ s t hm (S.childFin8 x) x.child.isLt
            (localDirection (S.label x.parent).2 d)
          rw [ha,←localDirection_rotate,hb] at ht
          obtain ⟨m,hclose,hchild⟩ := ht rfl
          apply S.taggedStep_external_eq y z (rotateTurn 2 d) s m q
          · simpa only [hyp,hyi,localDirection_rotate] using hclose
          · simpa only [hyp] using hq
          · exact hzp
          · simpa only [hyp] using hzi.trans hchild.symm
  | external s n =>
      obtain ⟨q,hq,hyp,hyi⟩ := S.taggedStep_external_end x y d s n ha hy
      let t := macroSide (S.label q).2 (opposite (macroSide (S.label x.parent).2 s))
      have hm := S.coarse_mating_marks hs x.parent q s hq
      cases hb : portAction (S.label x.parent).1 (S.childFin8 x)
          (localDirection (S.label x.parent).2 (rotateTurn 1 d)) with
      | internal j =>
          obtain ⟨hzp,hzi⟩ := S.taggedStep_internal_end x z _ j hb hz
          have ht := hpairs _ _ s t hm (S.childFin8 x) x.child.isLt
            (localDirection (S.label x.parent).2 d)
          rw [ha,←localDirection_rotate,hb] at ht
          obtain ⟨m,hclose,hchild⟩ := ht rfl
          have hclose' : portAction (S.label q).1 (matingPort (S.label q).1 t n).1
              (localDirection (S.label q).2 (rotateTurn 2 d)) = .external t m := by
            simpa only [←localDirection_rotate,t,seamLocal_direction] using hclose
          have hback : S.step (macroSide (S.label q).2 t) q = some x.parent := by
            dsimp [t]
            rw [macroSide_involutive]
            exact hs.opposite_inverse _ _ _ hq
          apply S.taggedStep_external_eq y z (rotateTurn 2 d) t m x.parent
          · simpa only [hyp,hyi] using hclose'
          · simpa only [hyp] using hback
          · exact hzp
          · simpa only [hyp,t,macroSide_return] using hzi.trans hchild.symm
      | external a h =>
          obtain ⟨r,hr,hzp,hzi⟩ := S.taggedStep_external_end x z _ a h hb hz
          have hb' : portAction (S.label x.parent).1 (S.childFin8 x)
              (rotateTurn 1 (localDirection (S.label x.parent).2 d)) = .external a h := by
            simpa only [localDirection_rotate] using hb
          rcases external_corner_same_or_next _ _ _ s a n h x.child.isLt ha hb' with heq | hnext
          · subst a
            have hqr : q = r := Option.some.inj (hq.symm.trans hr)
            rw [←hqr] at hr hzp hzi
            have ht := hpairs _ _ s t hm (S.childFin8 x) x.child.isLt
              (localDirection (S.label x.parent).2 d)
            rw [ha,←localDirection_rotate,hb] at ht
            have hclose := ht rfl rfl
            have hclose' : portAction (S.label q).1 (matingPort (S.label q).1 t n).1
                (localDirection (S.label q).2 (rotateTurn 2 d)) =
                .internal (matingPort (S.label q).1 t h).1 := by
              simpa only [←localDirection_rotate,t,seamLocal_direction] using hclose
            apply S.taggedStep_internal_eq y z (rotateTurn 2 d) (matingPort (S.label q).1 t h).1
            · simpa only [hyp,hyi] using hclose'
            · exact hzp.trans hyp.symm
            · exact hzi
          · subst a
            let u := macroSide (S.label r).2
              (opposite (macroSide (S.label x.parent).2 (rotateTurn 1 s)))
            have hm' := S.coarse_mating_marks hs x.parent r (rotateTurn 1 s) hr
            have hqr : S.step (macroSide (S.label q).2 (rotateTurn 5 t)) q = some r := by
              rw [show macroSide (S.label q).2 (rotateTurn 5 t) =
                  rotateTurn 4 (macroSide (S.label x.parent).2 s) from macroSide_triangle_left _ _ _]
              apply S.reversed_triangle hs _ _ _ _ hq
              simpa only [macroSide_next] using hr
            have hmqr : macroLabel (S.label q).1 (rotateTurn 5 t) =
                -macroLabel (S.label r).1 (rotateTurn 1 u) := by
              have hh := S.coarse_mating_marks hs q r (rotateTurn 5 t) hqr
              simpa only [t,u,macroSide_triangle_right] using hh
            have ht := htriples _ s _ t hm _ u hm' hmqr
              (S.childFin8 x) x.child.isLt (localDirection (S.label x.parent).2 d)
            rw [ha,←localDirection_rotate,hb] at ht
            obtain ⟨j,hclose,hchild⟩ := ht rfl rfl
            have hclose' : portAction (S.label q).1 (matingPort (S.label q).1 t n).1
                (localDirection (S.label q).2 (rotateTurn 2 d)) = .external (rotateTurn 5 t) j := by
              simpa only [←localDirection_rotate,t,seamLocal_direction] using hclose
            apply S.taggedStep_external_eq y z (rotateTurn 2 d) (rotateTurn 5 t) j r
            · simpa only [hyp,hyi] using hclose'
            · simpa only [hyp] using hqr
            · exact hzp
            · simpa only [hyp,t,u,macroSide_triangle_right] using hzi.trans hchild.symm

end SpectreFinite.HexSearch.PartialMarkedHexSystem
