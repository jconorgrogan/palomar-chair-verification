module
public import RegisteredPrime.OuterInterface
@[expose] public section
namespace RegisteredPrime

/-- The two permitted wall masks at the specified actual contact axis. -/
def WallMaskAt {p : Nat} (D : Mask p) (j : Fin p) : Prop :=
  ∃ b : Bool, ∀ i, D i = if i = j then !b else b

theorem wall_geometry_mask_at {p : Nat} (q : Pose p) (hw : WallGeometry q)
    (j : Fin p) (s : Bool) (hb : boxLower q = wallBox j s) : WallMaskAt q.frame.negative j := by
  obtain ⟨k, h | h⟩ := hw
  · obtain ⟨he, hs⟩ := wallBox_injective (hb.symm.trans h.1)
    subst k
    rcases h.2 with hh | hh
    · refine ⟨false, fun i => ?_⟩
      have hx := hole_from_box q i
      rw [congrFun hb i, congrFun hh i, hs] at hx
      by_cases hij : i = j
      · subst i
        cases hn : q.frame.negative j <;>
          simp [wallBox, unitAxis, bit, hn] at hx ⊢ <;> omega
      · cases hn : q.frame.negative i <;>
          simp [wallBox, unitAxis, bit, hij, hn] at hx ⊢ <;> omega
    · refine ⟨true, fun i => ?_⟩
      have hx := hole_from_box q i
      rw [congrFun hb i, congrFun hh i, hs] at hx
      by_cases hij : i = j
      · subst i
        cases hn : q.frame.negative j <;>
          simp [wallBox, unitAxis, bit, hn] at hx ⊢ <;> omega
      · cases hn : q.frame.negative i <;>
          simp [wallBox, unitAxis, bit, hij, hn] at hx ⊢ <;> omega
  · obtain ⟨he, hs⟩ := wallBox_injective (hb.symm.trans h.1)
    subst k
    rcases h.2 with hh | hh
    · refine ⟨false, fun i => ?_⟩
      have hx := hole_from_box q i
      rw [congrFun hb i, congrFun hh i, hs] at hx
      by_cases hij : i = j
      · subst i
        cases hn : q.frame.negative j <;>
          simp [wallBox, unitAxis, bit, hn] at hx ⊢ <;> omega
      · cases hn : q.frame.negative i <;>
          simp [wallBox, unitAxis, bit, hij, hn] at hx ⊢ <;> omega
    · refine ⟨true, fun i => ?_⟩
      have hx := hole_from_box q i
      rw [congrFun hb i, congrFun hh i, hs] at hx
      by_cases hij : i = j
      · subst i
        cases hn : q.frame.negative j <;>
          simp [wallBox, unitAxis, bit, hn] at hx ⊢ <;> omega
      · cases hn : q.frame.negative i <;>
          simp [wallBox, unitAxis, bit, hij, hn] at hx ⊢ <;> omega

theorem relative_adjacent_box_axis {p : Nat} (q r : Pose p) (j : Fin p)
    (hj : boxLower r j = boxLower q j + 2 ∨ boxLower q j = boxLower r j + 2)
    (ht : ∀ i, i ≠ j → boxLower q i = boxLower r i) :
    ∃ s : Bool, boxLower (q.relative r) = wallBox (q.frame.perm j) s := by
  rcases hj with hj | hj
  · refine ⟨!(q.frame.negative j), ?_⟩
    funext i
    rw [relative_boxLower]
    by_cases hij : i = q.frame.perm j
    · subst i
      rw [q.frame.left_inverse]
      cases hn : q.frame.negative j <;> simp [wallBox, RegisteredFrame.sign, hn] <;> omega
    · have hne : q.frame.inverse i ≠ j := by
        intro he
        apply hij
        have hh := congrArg q.frame.perm he
        rwa [q.frame.right_inverse] at hh
      rw [ht _ hne]
      simp [wallBox, hij]
  · refine ⟨q.frame.negative j, ?_⟩
    funext i
    rw [relative_boxLower]
    by_cases hij : i = q.frame.perm j
    · subst i
      rw [q.frame.left_inverse]
      cases hn : q.frame.negative j <;> simp [wallBox, RegisteredFrame.sign, hn] <;> omega
    · have hne : q.frame.inverse i ≠ j := by
        intro he
        apply hij
        have hh := congrArg q.frame.perm he
        rwa [q.frame.right_inverse] at hh
      rw [ht _ hne]
      simp [wallBox, hij]

/-- The signed mask restriction is transported to the actual world interface
axis; no assumption about the unsigned coordinate permutation is needed. -/
theorem relative_wall_mask_at {p : Nat} (q r : Pose p) (j : Fin p)
    (hj : boxLower r j = boxLower q j + 2 ∨ boxLower q j = boxLower r j + 2)
    (ht : ∀ i, i ≠ j → boxLower q i = boxLower r i)
    (hw : WallGeometry (q.relative r)) :
    WallMaskAt (fun i => xor (q.frame.negative i) (r.frame.negative i)) j := by
  obtain ⟨s, hs⟩ := relative_adjacent_box_axis q r j hj ht
  obtain ⟨b, hb⟩ := wall_geometry_mask_at _ hw (q.frame.perm j) s hs
  refine ⟨b, fun i => ?_⟩
  have h := hb (q.frame.perm i)
  rw [relative_negative, q.frame.left_inverse] at h
  have he : q.frame.perm i = q.frame.perm j ↔ i = j := by
    constructor
    · intro he
      have h' := congrArg q.frame.inverse he
      simpa only [q.frame.left_inverse] using h'
    · exact congrArg q.frame.perm
  simpa only [he] using h

end RegisteredPrime
