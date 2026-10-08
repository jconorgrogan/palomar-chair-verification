module
public import RegisteredPrime.CellDissection
@[expose] public section
namespace RegisteredPrime
noncomputable def childIndexInverse (P : Parameters) (r : Role P.p) (j : Fin P.p) : Fin P.p :=
  Classical.choose (childIndex_surjective P r j)
@[simp] theorem childIndex_right_inverse (P : Parameters) (r : Role P.p) (j : Fin P.p) :
    childIndex P r (childIndexInverse P r j) = j :=
  Classical.choose_spec (childIndex_surjective P r j)
@[simp] theorem childIndex_left_inverse (P : Parameters) (r : Role P.p) (i : Fin P.p) :
    childIndexInverse P r (childIndex P r i) = i :=
  childIndex_injective P r _ _ (childIndex_right_inverse P r (childIndex P r i))
def ChildOccupies (P : Parameters) (r : Role P.p) (y : Cell P.p) : Prop :=
  ∃ x, UnitChairCell x ∧ childCell P r x = y
theorem outer_image_iff (P : Parameters) (A : Mask P.p) (hA : Proper A) (y : Cell P.p) :
    ChildOccupies P (.outer A hA) y ↔ OuterCell A y := by
  classical
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact outer_image_cell P A hA x hx
  · intro hy
    let r : Role P.p := .outer A hA
    let x : Cell P.p := fun j =>
      let i := childIndexInverse P r j
      if A i then 3 - y i else y i
    have hdigits : ∀ j, x j = 0 ∨ x j = 1 := by
      intro j
      have h := hy.1 (childIndexInverse P r j)
      dsimp [x]
      cases ha : A (childIndexInverse P r j) <;> simp [bit, ha] at h ⊢ <;> omega
    have himage : childCell P (.outer A hA) x = y := by
      funext i
      rw [outer_cell_formula]
      have he : x (childIndex P r i) = if A i then 3 - y i else y i := by
        simp [x]
      change (if A i then 3 - x (childIndex P r i) else x (childIndex P r i)) = y i
      rw [he]
      cases A i <;> simp <;> omega
    have hzero : ∃ j, x j = 0 := by
      apply Classical.byContradiction
      intro hn
      have hone : x = fun _ => 1 := by
        funext j
        obtain h | h := hdigits j
        · exact False.elim (hn ⟨j, h⟩)
        · exact h
      have hh := himage
      rw [hone, outer_cell_hole] at hh
      exact hy.2 (fun i => (congrFun hh i).symm)
    exact ⟨x, ⟨hdigits, hzero⟩, himage⟩
theorem central_image_iff (P : Parameters) (y : Cell P.p) :
    ChildOccupies P .central y ↔ CentralCell y := by
  classical
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact central_image_cell P x hx
  · intro hy
    let x : Cell P.p := fun j => y (childIndexInverse P .central j) - 1
    have hdigits : ∀ j, x j = 0 ∨ x j = 1 := by
      intro j
      have h := hy.1 (childIndexInverse P .central j)
      dsimp [x]
      omega
    have hzero : ∃ j, x j = 0 := by
      obtain ⟨i, hi⟩ := hy.2
      exact ⟨childIndex P .central i, by simp [x, hi]⟩
    refine ⟨x, ⟨hdigits, hzero⟩, ?_⟩
    funext i
    rw [central_cell_formula]
    simp [x]
    omega
theorem exact_child_cover (P : Parameters) (y : Cell P.p) :
    DoubledChairCell y ↔ ∃ r : Role P.p, ChildOccupies P r y := by
  rw [doubled_cell_dissection]
  constructor
  · rintro (h | ⟨A, hp, h⟩)
    · exact ⟨.central, (central_image_iff P y).mpr h⟩
    · exact ⟨.outer A hp, (outer_image_iff P A hp y).mpr h⟩
  · rintro ⟨r, hr⟩
    cases r with
    | central => exact Or.inl ((central_image_iff P y).mp hr)
    | outer A hp => exact Or.inr ⟨A, hp, (outer_image_iff P A hp y).mp hr⟩
theorem exact_child_unique (P : Parameters) (y : Cell P.p) (r s : Role P.p)
    (hr : ChildOccupies P r y) (hs : ChildOccupies P s y) : r = s := by
  cases r with
  | central =>
    cases s with
    | central => rfl
    | outer B hB =>
      exact False.elim (outer_central_disjoint ((outer_image_iff P B hB y).mp hs)
        ((central_image_iff P y).mp hr))
  | outer A hA =>
    cases s with
    | central =>
      exact False.elim (outer_central_disjoint ((outer_image_iff P A hA y).mp hr)
        ((central_image_iff P y).mp hs))
    | outer B hB =>
      have he := outer_role_unique ((outer_image_iff P A hA y).mp hr)
        ((outer_image_iff P B hB y).mp hs)
      cases he
      rfl
theorem exact_dissection (P : Parameters) (y : Cell P.p) (hy : DoubledChairCell y) :
    ∃ r : Role P.p, ChildOccupies P r y ∧ ∀ s, ChildOccupies P s y → s = r := by
  obtain ⟨r, hr⟩ := (exact_child_cover P y).mp hy
  exact ⟨r, hr, fun s hs => exact_child_unique P y s r hs hr⟩
end RegisteredPrime
