module

public import SpectreFinite.ParentOwnershipCoverage

@[expose] public section


/-! Exact parent patterns reuse childrenTable, never a second transcription.
Finite-list properties and their occurrence-conditional transfers do not
establish boundary vertex locations or physical substitution. -/
namespace SpectreFinite.HexSearch.ParentOwnership

def childPatch (k : TileKind) : Patch :=
  (children k).map (fun a => (pos a,(a.kind,a.turn)))

/-- Ordered complete owned region of a turn-zero Gamma at the origin. -/
def rootParent (f : Position → State) : Patch :=
  ((primaryOffsets ++ [secondaryOffset]).filter
    (fun x => decide ((0,0) ∈ owners f x))).map (fun x => (x,f x))

theorem selected_by_origin_positions (f : Position → State)
    (hf : f (0,0) = (0,0)) (x : Position) (h : (0,0) ∈ owners f x) :
    x ∈ primaryOffsets ++ [secondaryOffset] := by
  obtain ⟨_,d,hd,he⟩ := selected_owner_positions f x (0,0) h
  rw [hf] at he
  have hx : x = d := by simpa [rotatePosition,addPos] using he
  rw [hx]
  exact hd

/-- The eight-position construction omits no cell owned by this Gamma. -/
theorem mem_rootParent_iff (f : Position → State) (hf : f (0,0) = (0,0))
    (x : Position) (s : State) :
    (x,s) ∈ rootParent f ↔ (0,0) ∈ owners f x ∧ s = f x := by
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := List.mem_map.mp h
    have hx : y = x := congrArg Prod.fst he
    subst y
    exact ⟨of_decide_eq_true (List.mem_filter.mp hy).2,(congrArg Prod.snd he).symm⟩
  · rintro ⟨ho,rfl⟩
    apply List.mem_map.mpr
    exact ⟨x,List.mem_filter.mpr
      ⟨selected_by_origin_positions f hf x ho,decide_eq_true ho⟩,rfl⟩

theorem rootParent_local (f g : Position → State)
    (hs : ∀ x ∈ primaryOffsets ++ [secondaryOffset], f x = g x)
    (ho : ∀ x ∈ primaryOffsets ++ [secondaryOffset], owners f x = owners g x) :
    rootParent f = rootParent g := by
  have hfilter : (primaryOffsets ++ [secondaryOffset]).filter
      (fun x => decide ((0,0) ∈ owners f x)) =
      (primaryOffsets ++ [secondaryOffset]).filter
      (fun x => decide ((0,0) ∈ owners g x)) := by
    apply List.filter_congr
    intro x hx
    rw [ho x hx]
  unfold rootParent
  rw [hfilter]
  apply List.map_congr_left
  intro x hx
  rw [hs x (List.mem_filter.mp hx).1]

theorem parent_offsets_radiusThree :
    ∀ x ∈ primaryOffsets ++ [secondaryOffset], x ∈ hexRegion 3 := by decide

theorem parent_offsets_radiusFive :
    ∀ x ∈ primaryOffsets ++ [secondaryOffset], x ∈ hexRegion 5 := by decide

/-- All state reads and all backward candidate lookups are in the actual
radius-five extraction. The default Gamma state is not used. -/
theorem rootParent_extract (f : Position → State) (center : Position) :
    rootParent (patchState (extract f center (hexRegion 5))) =
      rootParent (shiftedField f center) := by
  apply rootParent_local
  · intro x hx
    exact patchState_restriction _ _ x (parent_offsets_radiusFive x hx)
  · intro x hx
    exact owners_extract f center (hexRegion 5) x
      (radiusThree_candidates_covered x (parent_offsets_radiusThree x hx))

def rootParentKinds (f : Position → State) : List TileKind :=
  (List.finRange 9).filter (fun k => decide (rootParent f = childPatch k))

/-- Exactly one of the nine literal author patterns is selected. -/
def ListedRootParent (f : Position → State) : Prop := (rootParentKinds f).length = 1
instance (f : Position → State) : Decidable (ListedRootParent f) :=
  inferInstanceAs (Decidable (_ = _))

theorem listedRootParent_iff (f : Position → State) :
    ListedRootParent f ↔ ∃ k, rootParentKinds f = [k] := List.length_eq_one_iff

theorem listedRootParent_selected (f : Position → State) (h : ListedRootParent f) :
    ∃ k : TileKind, rootParent f = childPatch k ∧
      ∀ j : TileKind, rootParent f = childPatch j → j = k := by
  obtain ⟨k,hk⟩ := (listedRootParent_iff f).mp h
  have mem_iff : ∀ j : TileKind, j ∈ rootParentKinds f ↔ rootParent f = childPatch j := by
    intro j
    simp [rootParentKinds]
  refine ⟨k,(mem_iff k).mp (by simp [hk]),?_⟩
  intro j hj
  have hm := (mem_iff j).mpr hj
  simpa [hk] using hm

/-- Conditional shape transfer for an actual Gamma anchor in turn-zero
coordinates. Ownership outside the displayed support is excluded by
mem_rootParent_iff, not assumed from the finite list. -/
theorem listed_parent_of_radiusFive_certificate (family : List Patch)
    (hcert : ∀ p ∈ family, patchState p (0,0) = (0,0) → ListedRootParent (patchState p))
    (f : Position → State) (hocc : OccurrenceComplete f (hexRegion 5) family)
    (center : Position) (hroot : f center = (0,0)) :
    ListedRootParent (shiftedField f center) := by
  have hs : patchState (extract f center (hexRegion 5)) (0,0) = (0,0) := by
    change patchState (restriction (shiftedField f center) (hexRegion 5)) (0,0) = (0,0)
    rw [patchState_restriction (shiftedField f center) (hexRegion 5) (0,0) (by decide)]
    simpa [shiftedField,addPos] using hroot
  have h := hcert _ (hocc center) hs
  unfold ListedRootParent rootParentKinds at h ⊢
  rw [rootParent_extract f center] at h
  exact h

#print axioms mem_rootParent_iff
#print axioms rootParent_extract
#print axioms listedRootParent_selected
#print axioms listed_parent_of_radiusFive_certificate
end SpectreFinite.HexSearch.ParentOwnership
