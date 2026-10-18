module

public import SpectreFinite.TaggedHexRefinement
public import SpectreFinite.ForwardPortConsequences

@[expose] public section


/-! Boundary accounting for the actual tagged substitution. -/
namespace SpectreFinite.HexSearch.PartialMarkedHexSystem
open Boundary ForwardSubstitution

theorem coarse_mating_marks (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (p q : S.Cell) (s : Fin 6)
    (h : S.step (macroSide (S.label p).2 s) p = some q) :
    macroLabel (S.label p).1 s =
      -macroLabel (S.label q).1 (macroSide (S.label q).2
        (opposite (macroSide (S.label p).2 s))) := by
  let D := macroSide (S.label p).2 s
  calc
    macroLabel (S.label p).1 s =
        macroLabel (S.label p).1 (macroSide (S.label p).2 D) := by
      rw [show macroSide (S.label p).2 D = s from macroSide_involutive _ _]
    _ = S.mark p D := macroSide_mark _ _ _
    _ = -S.mark q (opposite D) := hs.matching D p q h
    _ = -macroLabel (S.label q).1 (macroSide (S.label q).2 (opposite D)) :=
      congrArg Neg.neg (macroSide_mark _ _ _).symm

theorem taggedStep_none_iff (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (x : ChildTag S) (d : Fin 6) :
    S.taggedStep d x = none ↔
      ∃ s n : Fin 6,
        portAction (S.label x.parent).1 (S.childFin8 x)
          (localDirection (S.label x.parent).2 d) = .external s n ∧
        S.step (macroSide (S.label x.parent).2 s) x.parent = none := by
  constructor
  · intro h
    cases ha : portAction (S.label x.parent).1 (S.childFin8 x)
        (localDirection (S.label x.parent).2 d) with
    | internal j =>
        have hj := portAction_internal_bound _ _ j _ x.child.isLt ha
        simp [taggedStep, ha, tagAt, hj] at h
    | external s n =>
        refine ⟨s,n,rfl,?_⟩
        cases hq : S.step (macroSide (S.label x.parent).2 s) x.parent with
        | none => rfl
        | some q =>
            have hm := S.coarse_mating_marks hs x.parent q s hq
            have hn := portAction_external_slot_lt _ _ _ s n x.child.isLt ha
            have hj := matingPort_bound _ _ _ _ n hm hn
            simp [taggedStep, ha, hq, tagAt, hj] at h
  · rintro ⟨s,n,ha,hq⟩
    simp [taggedStep, ha, hq]

/-- An exposed child port is addressed by its old exposed parent port and its
position (at most six) in that parent's macro-segment. -/
def boundaryAddress (S : PartialMarkedHexSystem) (p : S.refine.Cell × Fin 6) :
    (S.Cell × Fin 6) × Fin 6 :=
  let x := S.decodeChild p.1
  match portAction (S.label x.parent).1 (S.childFin8 x)
      (localDirection (S.label x.parent).2 p.2) with
  | .internal _ => ((x.parent,0),0)
  | .external s n => ((x.parent,macroSide (S.label x.parent).2 s),n)

def boundarySlots (S : PartialMarkedHexSystem) : List ((S.Cell × Fin 6) × Fin 6) :=
  S.boundaryPorts.flatMap fun p => (List.finRange 6).map fun n => (p,n)

theorem boundaryAddress_mem (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (p : S.refine.Cell × Fin 6) (hp : p ∈ S.refine.boundaryPorts) :
    S.boundaryAddress p ∈ S.boundarySlots := by
  have hn := (S.refine.mem_boundaryPorts p.1 p.2).mp hp
  have hn' : S.taggedStep p.2 (S.decodeChild p.1) = none := by
    simpa [refine] using hn
  obtain ⟨s,n,ha,hq⟩ := (S.taggedStep_none_iff hs _ _).mp hn'
  simp only [boundaryAddress, ha]
  apply List.mem_flatMap.mpr
  refine ⟨(_, _),(S.mem_boundaryPorts _ _).mpr hq,?_⟩
  exact List.mem_map.mpr ⟨n,List.mem_finRange _,rfl⟩

theorem external_address_injective (S : PartialMarkedHexSystem)
    (x y : ChildTag S) (d e s t n m : Fin 6)
    (hx : portAction (S.label x.parent).1 (S.childFin8 x)
      (localDirection (S.label x.parent).2 d) = .external s n)
    (hy : portAction (S.label y.parent).1 (S.childFin8 y)
      (localDirection (S.label y.parent).2 e) = .external t m)
    (h : ((x.parent,macroSide (S.label x.parent).2 s),n) =
      ((y.parent,macroSide (S.label y.parent).2 t),m)) : x = y ∧ d = e := by
  rcases x with ⟨p,i⟩
  rcases y with ⟨q,j⟩
  have hp : p = q := congrArg (fun z => z.1.1) h
  subst q
  have hn : n = m := congrArg Prod.snd h
  subst m
  have hd := congrArg (fun z => z.1.2) h
  have hst : s = t := by
    have h' := congrArg (macroSide (S.label p).2) hd
    simpa only [macroSide_involutive] using h'
  subst t
  have hij := portAction_external_injective (S.label p).1
    (S.childFin8 ⟨p,i⟩) (S.childFin8 ⟨p,j⟩) _ _ s n i.isLt j.isLt hx hy
  have hi : i = j := Fin.ext (congrArg (fun z : Fin 8 => z.val) hij.1)
  have he : d = e := by
    have h' := congrArg (rotateTurn (inverseTurn (S.label p).2)) hij.2
    simpa only [localDirection, rotateTurn_inverse] using h'
  exact ⟨by cases hi; rfl,he⟩

theorem boundaryAddress_injective_on (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (a b : S.refine.Cell × Fin 6) (ha : a ∈ S.refine.boundaryPorts)
    (hb : b ∈ S.refine.boundaryPorts) (h : S.boundaryAddress a = S.boundaryAddress b) :
    a = b := by
  have ha' : S.taggedStep a.2 (S.decodeChild a.1) = none := by
    simpa [refine] using (S.refine.mem_boundaryPorts a.1 a.2).mp ha
  have hb' : S.taggedStep b.2 (S.decodeChild b.1) = none := by
    simpa [refine] using (S.refine.mem_boundaryPorts b.1 b.2).mp hb
  obtain ⟨s,n,has,_⟩ := (S.taggedStep_none_iff hs _ _).mp ha'
  obtain ⟨t,m,hbs,_⟩ := (S.taggedStep_none_iff hs _ _).mp hb'
  simp only [boundaryAddress,has,hbs] at h
  have heq := S.external_address_injective _ _ _ _ s t n m has hbs h
  apply Prod.ext
  · have h' := congrArg S.encodeChild heq.1
    exact (S.encode_decodeChild a.1).symm.trans (h'.trans (S.encode_decodeChild b.1))
  · exact heq.2

theorem ports_nodup (S : PartialMarkedHexSystem) : S.ports.Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro p _
    apply List.pairwise_map.mpr
    apply (List.nodup_finRange 6).imp
    intro d e h he
    exact h (congrArg Prod.snd he)
  · apply (List.nodup_finRange S.cellCount).imp
    intro p q hpq a ha b hb hab
    obtain ⟨d,_,hda⟩ := List.mem_map.mp ha
    obtain ⟨e,_,heb⟩ := List.mem_map.mp hb
    exact hpq (by have h := congrArg Prod.fst hab; simpa [← hda, ← heb] using h)

theorem boundaryPorts_nodup (S : PartialMarkedHexSystem) : S.boundaryPorts.Nodup :=
  S.ports_nodup.filter _

theorem boundarySlots_length (S : PartialMarkedHexSystem) :
    S.boundarySlots.length = S.boundaryPorts.length*6 := by
  have hconst : ∀ l : List (S.Cell × Fin 6), (l.map (fun _ => 6)).sum = l.length*6 := by
    intro l
    induction l with
    | nil => rfl
    | cons p ps ih => simp [ih, Nat.add_mul, Nat.add_comm]
  simpa [boundarySlots, List.length_flatMap] using hconst S.boundaryPorts

theorem refine_boundaryCount_le_six (S : PartialMarkedHexSystem) (hs : S.WellFormed) :
    S.refine.boundaryPorts.length ≤ S.boundaryPorts.length*6 := by
  have hn : (S.refine.boundaryPorts.map S.boundaryAddress).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ S.refine.boundaryPorts_nodup
    intro a b ha hb hne heq
    exact hne (S.boundaryAddress_injective_on hs a b ha hb heq)
  have hsub : S.refine.boundaryPorts.map S.boundaryAddress ⊆ S.boundarySlots := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    exact S.boundaryAddress_mem hs p hp
  have hlen := hn.length_le_of_subset hsub
  simpa only [List.length_map, boundarySlots_length] using hlen

end SpectreFinite.HexSearch.PartialMarkedHexSystem
