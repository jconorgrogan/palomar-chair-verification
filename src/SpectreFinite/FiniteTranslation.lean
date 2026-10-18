module

public import SpectreFinite.ParentPartition

@[expose] public section


/-! A nonempty finite set of native axial cells has trivial translation
stabilizer. This elementary obstruction will be used for individual blocks
of a genuinely constructed hierarchy. -/
namespace SpectreFinite.HexSearch.FiniteTranslation
open ParentOwnership

private theorem int_sum_perm {xs ys : List Int} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => simp
  | cons _ _ ih => simp [ih]
  | swap => simpa [List.sum_cons] using Int.add_left_comm ..
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem shifted_coordinate_sum (A : List Position) (c : Position → Int)
    (v : Position) (hc : ∀ x, c (addPos x v) = c x + c v) :
    ((A.map (fun x => addPos x v)).map c).sum = (A.map c).sum + (A.length : Int)*c v := by
  induction A with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Int.natCast_add,
      Int.natCast_one,Int.add_mul,Int.one_mul,hc,ih]
    omega

theorem translate_perm_of_invariant (A : List Position) (ha : A.Nodup) (v : Position)
    (hinv : ∀ x, x ∈ A ↔ addPos x v ∈ A) :
    (A.map (fun x => addPos x v)).Perm A := by
  have hmap : (A.map (fun x => addPos x v)).Nodup :=
    List.Pairwise.map _ (fun x y h he => h (by
      apply Prod.ext
      · have hq := congrArg Prod.fst he; simp only [addPos] at hq ⊢; omega
      · have hr := congrArg Prod.snd he; simp only [addPos] at hr ⊢; omega)) ha
  apply (List.perm_ext_iff_of_nodup hmap ha).mpr
  intro x
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := List.mem_map.mp h
    rw [← he]
    exact (hinv y).mp hy
  · intro h
    let y := subPos x v
    have he : addPos y v = x := by apply Prod.ext <;> simp only [y,subPos,addPos] <;> omega
    exact List.mem_map.mpr ⟨y,(hinv y).mpr (he.symm ▸ h),he⟩

/-- Exact setwise invariance of a nonempty finite block forces both axial
coordinates of the translation vector to vanish. -/
theorem translation_eq_zero (A : List Position) (ha : A.Nodup) (hne : A ≠ [])
    (v : Position) (hinv : ∀ x, x ∈ A ↔ addPos x v ∈ A) : v = (0,0) := by
  have hp := translate_perm_of_invariant A ha v hinv
  have hlen : (A.length : Int) ≠ 0 := by
    have hn : A.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
    omega
  have coord : ∀ c : Position → Int,
      (∀ x, c (addPos x v) = c x + c v) → c v = 0 := by
    intro c hc
    have he := int_sum_perm (hp.map c)
    rw [shifted_coordinate_sum A c v hc] at he
    have hm : (A.length : Int)*c v = 0 := by omega
    exact (Int.mul_eq_zero.mp hm).resolve_left hlen
  exact Prod.ext (coord Prod.fst (fun _ => rfl)) (coord Prod.snd (fun _ => rfl))

end SpectreFinite.HexSearch.FiniteTranslation
