module

public import SpectreFinite.ParentRotation

@[expose] public section


/-! The actual selected-owner relation partitions every field with unique
ownership. Its translation covariance is derived from the algorithm; no
parent-period preservation assumption is introduced. This module does not
assert that the parent partition can yet be iterated. -/
namespace SpectreFinite.HexSearch.ParentOwnership

/-- Literal translation period of all marked states. -/
def FieldPeriod (f : Position → State) (v : Position) : Prop :=
  ∀ x, f (addPos v x) = f x

/-- Membership of a native cell in the actual parent anchored at `a`. -/
def ParentCell (f : Position → State) (a x : Position) : Prop := a ∈ owners f x

theorem gamma_primary_self (f : Position → State) (a : Position) (ha : (f a).1 = 0) :
    a ∈ primaryOwners f a := by
  apply (mem_primaryOwners_iff f a a).mpr
  refine ⟨ha,(0,0),by decide,?_⟩
  have h : rotatePosition (f a).2 (0,0) = (0,0) := by
    have ht := (f a).2.isLt
    unfold rotatePosition
    split <;> simp_all <;> omega
  simp [h,addPos]

theorem gamma_parent_self (f : Position → State) (a : Position) (ha : (f a).1 = 0) :
    ParentCell f a a := by
  have h := gamma_primary_self f a ha
  have hn : primaryOwners f a ≠ [] := by intro he; simp [he] at h
  simpa [ParentCell,owners,hn] using h

theorem parent_anchor_gamma (f : Position → State) (a x : Position)
    (h : ParentCell f a x) : (f a).1 = 0 :=
  (selected_owner_positions f x a h).1

theorem parent_cell_bounded (f : Position → State) (a x : Position)
    (h : ParentCell f a x) :
    ∃ d ∈ primaryOffsets ++ [secondaryOffset], x = addPos a (rotatePosition (f a).2 d) :=
  (selected_owner_positions f x a h).2

theorem parent_cells_cover (f : Position → State) (hu : ∀ x, UniqueAt f x)
    (x : Position) : ∃ a, ParentCell f a x := by
  obtain ⟨a,ha,_⟩ := uniqueAt_selected f x (hu x)
  exact ⟨a,ha⟩

theorem parent_cells_disjoint (f : Position → State) (hu : ∀ x, UniqueAt f x)
    (a b x : Position) (ha : ParentCell f a x) (hb : ParentCell f b x) : a = b := by
  obtain ⟨c,_,hc⟩ := uniqueAt_selected f x (hu x)
  exact (hc a ha).trans (hc b hb).symm

noncomputable def parentAnchor (f : Position → State) (hu : ∀ x, UniqueAt f x)
    (x : Position) : Position := Classical.choose (parent_cells_cover f hu x)

theorem parentAnchor_spec (f : Position → State) (hu : ∀ x, UniqueAt f x)
    (x : Position) : ParentCell f (parentAnchor f hu x) x :=
  Classical.choose_spec (parent_cells_cover f hu x)

theorem parentAnchor_eq_iff (f : Position → State) (hu : ∀ x, UniqueAt f x)
    (a x : Position) : parentAnchor f hu x = a ↔ ParentCell f a x := by
  constructor
  · intro h; rw [← h]; exact parentAnchor_spec f hu x
  · intro h; exact parent_cells_disjoint f hu _ _ x (parentAnchor_spec f hu x) h

theorem parentAnchor_gamma (f : Position → State) (hu : ∀ x, UniqueAt f x)
    (x : Position) : (f (parentAnchor f hu x)).1 = 0 :=
  parent_anchor_gamma f _ _ (parentAnchor_spec f hu x)

theorem parentAnchor_self (f : Position → State) (hu : ∀ x, UniqueAt f x)
    (a : Position) (ha : (f a).1 = 0) : parentAnchor f hu a = a :=
  (parentAnchor_eq_iff f hu a a).mpr (gamma_parent_self f a ha)

theorem fieldPeriod_shiftedField (f : Position → State) (v : Position)
    (hv : FieldPeriod f v) : shiftedField f v = f := by
  funext x; exact hv x

/-- A literal period preserves full parent membership, including the priority
rule distinguishing primary and secondary candidate anchors. -/
theorem parentCell_period_iff (f : Position → State) (v : Position)
    (hv : FieldPeriod f v) (a x : Position) :
    ParentCell f (addPos v a) (addPos v x) ↔ ParentCell f a x := by
  unfold ParentCell
  rw [mem_owners_translate_iff,fieldPeriod_shiftedField f v hv]

theorem parentAnchor_period (f : Position → State) (hu : ∀ x, UniqueAt f x)
    (v : Position) (hv : FieldPeriod f v) (x : Position) :
    parentAnchor f hu (addPos v x) = addPos v (parentAnchor f hu x) := by
  apply (parentAnchor_eq_iff f hu _ _).mpr
  exact (parentCell_period_iff f v hv _ _).mpr (parentAnchor_spec f hu x)

end SpectreFinite.HexSearch.ParentOwnership
