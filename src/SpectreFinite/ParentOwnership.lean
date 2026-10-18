module

public import SpectreFinite.RotatedWindows

@[expose] public section


/-!
The exact two-stage marked-hexagon assignment from arXiv:2305.17743v2,
section 5. Primary offsets are the seven common positions of childrenTable;
secondary assignment is used only when there is no primary owner.
All transfers below have an explicit finite-family occurrence hypothesis.
This module does not assert occurrence completeness of any supplied list,
parent-boundary vertex placement, physical realization, or aperiodicity.
-/
namespace SpectreFinite.HexSearch.ParentOwnership

def primaryOffsets : List Position :=
  [(0,0),(1,0),(0,1),(1,1),(0,-1),(1,-1),(2,-1)]

def secondaryOffset : Position := (2,-2)

def subPos (x y : Position) : Position := (x.1-y.1,x.2-y.2)

theorem subPos_eq_iff (x y a : Position) :
    subPos x y = a ↔ x = addPos a y := by
  rcases x with ⟨xq,xr⟩
  rcases y with ⟨yq,yr⟩
  rcases a with ⟨aq,ar⟩
  simp only [subPos, addPos, Prod.mk.injEq]
  omega

theorem subPos_translate (c x y : Position) :
    subPos (addPos c x) y = addPos c (subPos x y) := by
  apply Prod.ext <;> simp only [subPos, addPos] <;> omega

/-- Candidate anchors are constructed backwards from the query cell. A
candidate's hypothesized turn must equal the actual Gamma tile's turn. -/
def candidates (offsets : List Position) (x : Position) : List (Fin 6 × Position) :=
  (List.finRange 6).flatMap (fun t =>
    offsets.map (fun d => (t,subPos x (rotatePosition t d))))

def anchors (f : Position → State) (offsets : List Position) (x : Position) : List Position :=
  ((candidates offsets x).filter (fun a => decide (f a.2 = (0,a.1)))).map Prod.snd

def primaryOwners (f : Position → State) (x : Position) : List Position :=
  anchors f primaryOffsets x

def secondaryOwners (f : Position → State) (x : Position) : List Position :=
  anchors f [secondaryOffset] x

def owners (f : Position → State) (x : Position) : List Position :=
  if primaryOwners f x = [] then secondaryOwners f x else primaryOwners f x

/-- The first stage really is Gamma plus its seven rotated common offsets. -/
def PrimaryOwner (f : Position → State) (x a : Position) : Prop :=
  (f a).1 = 0 ∧ ∃ d ∈ primaryOffsets, x = addPos a (rotatePosition (f a).2 d)

/-- The possible secondary owner is at the one extra illustrated offset. -/
def SecondaryOwner (f : Position → State) (x a : Position) : Prop :=
  (f a).1 = 0 ∧ x = addPos a (rotatePosition (f a).2 secondaryOffset)

theorem mem_candidates_iff (offsets : List Position) (x : Position)
    (t : Fin 6) (a : Position) :
    (t,a) ∈ candidates offsets x ↔
      ∃ d ∈ offsets, a = subPos x (rotatePosition t d) := by
  constructor
  · intro h
    obtain ⟨u,_,hu⟩ := List.mem_flatMap.mp h
    obtain ⟨d,hd,he⟩ := List.mem_map.mp hu
    have ht : u = t := congrArg Prod.fst he
    subst u
    exact ⟨d,hd,(congrArg Prod.snd he).symm⟩
  · rintro ⟨d,hd,ha⟩
    apply List.mem_flatMap.mpr
    refine ⟨t,by simp,?_⟩
    exact List.mem_map.mpr ⟨d,hd,by rw [ha]⟩

theorem mem_anchors_iff (f : Position → State) (offsets : List Position)
    (x a : Position) :
    a ∈ anchors f offsets x ↔
      (f a).1 = 0 ∧ ∃ d ∈ offsets, x = addPos a (rotatePosition (f a).2 d) := by
  constructor
  · intro h
    obtain ⟨⟨t,b⟩, hb, he⟩ := List.mem_map.mp h
    change b = a at he
    subst b
    obtain ⟨hc,hf⟩ := List.mem_filter.mp hb
    have hf' : f a = (0,t) := of_decide_eq_true hf
    obtain ⟨d,hd,ha⟩ := (mem_candidates_iff offsets x t a).mp hc
    refine ⟨congrArg Prod.fst hf',d,hd,?_⟩
    rw [hf']
    exact (subPos_eq_iff x (rotatePosition t d) a).mp ha.symm
  · rintro ⟨hk,d,hd,hx⟩
    apply List.mem_map.mpr
    refine ⟨((f a).2,a),List.mem_filter.mpr ⟨?_,?_⟩,rfl⟩
    · apply (mem_candidates_iff offsets x (f a).2 a).mpr
      exact ⟨d,hd,((subPos_eq_iff x _ a).mpr hx).symm⟩
    · apply decide_eq_true
      apply Prod.ext
      · exact hk
      · rfl

theorem mem_primaryOwners_iff (f : Position → State) (x a : Position) :
    a ∈ primaryOwners f x ↔ PrimaryOwner f x a :=
  mem_anchors_iff f primaryOffsets x a

theorem mem_secondaryOwners_iff (f : Position → State) (x a : Position) :
    a ∈ secondaryOwners f x ↔ SecondaryOwner f x a := by
  simpa [secondaryOwners, SecondaryOwner] using mem_anchors_iff f [secondaryOffset] x a

/-- Every selected owner is an actual Gamma, and no cell outside its eight
possible rotated offsets can ever belong to it. -/
theorem selected_owner_positions (f : Position → State) (x a : Position)
    (h : a ∈ owners f x) :
    (f a).1 = 0 ∧ ∃ d ∈ primaryOffsets ++ [secondaryOffset],
      x = addPos a (rotatePosition (f a).2 d) := by
  unfold owners at h
  split at h
  · have hs := (mem_secondaryOwners_iff f x a).mp h
    exact ⟨hs.1,secondaryOffset,by simp,hs.2⟩
  · have hp := (mem_primaryOwners_iff f x a).mp h
    obtain ⟨d,hd,he⟩ := hp.2
    exact ⟨hp.1,d,List.mem_append_left _ hd,he⟩

/-- Explicit finite support needed for evaluating both assignment stages. -/
def CoversCandidates (domain : List Position) (x : Position) : Prop :=
  ∀ t : Fin 6, ∀ d ∈ primaryOffsets ++ [secondaryOffset],
    subPos x (rotatePosition t d) ∈ domain

instance (domain : List Position) (x : Position) : Decidable (CoversCandidates domain x) :=
  inferInstanceAs (Decidable (∀ t : Fin 6, ∀ d ∈ primaryOffsets ++ [secondaryOffset],
    subPos x (rotatePosition t d) ∈ domain))

theorem anchors_local (f g : Position → State) (offsets : List Position) (x : Position)
    (h : ∀ t : Fin 6, ∀ d ∈ offsets,
      f (subPos x (rotatePosition t d)) = g (subPos x (rotatePosition t d))) :
    anchors f offsets x = anchors g offsets x := by
  unfold anchors
  congr 1
  apply List.filter_congr
  intro a ha
  obtain ⟨d,hd,he⟩ := (mem_candidates_iff offsets x a.1 a.2).mp ha
  rw [he,h a.1 d hd]

theorem owners_local (f g : Position → State) (x : Position)
    (h : ∀ t : Fin 6, ∀ d ∈ primaryOffsets ++ [secondaryOffset],
      f (subPos x (rotatePosition t d)) = g (subPos x (rotatePosition t d))) :
    owners f x = owners g x := by
  have hp := anchors_local f g primaryOffsets x
    (fun t d hd => h t d (List.mem_append_left _ hd))
  have hs := anchors_local f g [secondaryOffset] x
    (fun t d hd => h t d (List.mem_append_right _ hd))
  simp only [owners, primaryOwners, secondaryOwners, hp, hs]
  rfl

/-- The total patch lookup's default is never used in this transfer. Every
queried anchor is required to lie in the extracted window's actual domain. -/
theorem owners_extract (f : Position → State) (center : Position)
    (domain : List Position) (x : Position) (hcov : CoversCandidates domain x) :
    owners (patchState (extract f center domain)) x = owners (shiftedField f center) x := by
  apply owners_local
  intro t d hd
  exact patchState_restriction (shiftedField f center) domain _ (hcov t d hd)


theorem candidates_translate (offsets : List Position) (c x : Position) :
    candidates offsets (addPos c x) =
      (candidates offsets x).map (fun a => (a.1,addPos c a.2)) := by
  simp [candidates, List.map_flatMap, List.map_map, Function.comp_def, subPos_translate]

theorem anchors_translate (f : Position → State) (offsets : List Position)
    (c x : Position) :
    anchors f offsets (addPos c x) =
      (anchors (shiftedField f c) offsets x).map (addPos c) := by
  simp [anchors, candidates_translate, List.filter_map, List.map_map,
    Function.comp_def, shiftedField]
  rfl

/-- The actual two-stage assignment commutes with every lattice translation. -/
theorem owners_translate (f : Position → State) (c x : Position) :
    owners f (addPos c x) = (owners (shiftedField f c) x).map (addPos c) := by
  unfold owners primaryOwners secondaryOwners
  rw [anchors_translate, anchors_translate]
  simp only [List.map_eq_nil_iff]
  split <;> rfl

/-- A singleton owner list proves both existence and uniqueness of the
selected anchor, without selecting arbitrary witnesses in the algorithm. -/
def UniqueAt (f : Position → State) (x : Position) : Prop :=
  (owners f x).length = 1

instance (f : Position → State) (x : Position) : Decidable (UniqueAt f x) :=
  inferInstanceAs (Decidable (_ = _))

theorem uniqueAt_iff (f : Position → State) (x : Position) :
    UniqueAt f x ↔ ∃ a, owners f x = [a] := by
  exact List.length_eq_one_iff

theorem uniqueAt_selected (f : Position → State) (x : Position) (h : UniqueAt f x) :
    ∃ a, a ∈ owners f x ∧ ∀ b, b ∈ owners f x → b = a := by
  obtain ⟨a,ha⟩ := (uniqueAt_iff f x).mp h
  exact ⟨a,by simp [ha],by simp [ha]⟩

theorem uniqueAt_primary_stage (f : Position → State) (x : Position)
    (h : UniqueAt f x) : (primaryOwners f x).length ≤ 1 := by
  unfold UniqueAt owners at h
  split at h
  · rename_i he
    simp [he]
  · omega

/-- This is the precise conditional bridge from finite window certificates
to unique ownership in a whole field. No legal-field hypothesis can replace
the explicit occurrence-completeness premise. -/
theorem unique_ownership_of_occurrenceComplete
    (domain : List Position) (family : List Patch)
    (hcov : CoversCandidates domain (0,0))
    (hcert : ∀ p ∈ family, UniqueAt (patchState p) (0,0))
    (f : Position → State) (hocc : OccurrenceComplete f domain family) :
    ∀ x : Position, UniqueAt f x := by
  intro x
  have h := hcert (extract f x domain) (hocc x)
  unfold UniqueAt at h ⊢
  rw [owners_extract f x domain (0,0) hcov] at h
  have ht := owners_translate f x (0,0)
  have hz : addPos x (0,0) = x := by simp [addPos]
  rw [hz] at ht
  rw [ht,List.length_map]
  exact h

#print axioms owners_translate
#print axioms unique_ownership_of_occurrenceComplete

#print axioms mem_anchors_iff
#print axioms owners_local
#print axioms owners_extract
end SpectreFinite.HexSearch.ParentOwnership
