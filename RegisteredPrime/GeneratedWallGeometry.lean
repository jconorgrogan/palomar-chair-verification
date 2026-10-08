module
public import RegisteredPrime.ColoredWallMask
@[expose] public section
namespace RegisteredPrime
theorem wall_geometry_of_box_mask {p : Nat} (e : Pose p) (j : Fin p) (side color : Bool)
    (hbox : boxLower e = wallBox j side)
    (hmask : ∀ i, e.frame.negative i = if i = j then !color else color) : WallGeometry e := by
  refine ⟨j, ?_⟩
  cases side with
  | false =>
    right
    refine ⟨hbox, ?_⟩
    cases color with
    | false =>
      left
      funext i
      rw [hole_from_box, hmask, congrFun hbox i]
      by_cases hi : i = j <;> simp [wallBox, unitAxis, bit, hi]
    | true =>
      right
      funext i
      rw [hole_from_box, hmask, congrFun hbox i]
      by_cases hi : i = j <;> simp [wallBox, unitAxis, bit, hi]
  | true =>
    left
    refine ⟨hbox, ?_⟩
    cases color with
    | false =>
      left
      funext i
      rw [hole_from_box, hmask, congrFun hbox i]
      by_cases hi : i = j <;> simp [wallBox, unitAxis, bit, hi]
    | true =>
      right
      funext i
      rw [hole_from_box, hmask, congrFun hbox i]
      by_cases hi : i = j <;> simp [wallBox, unitAxis, bit, hi]
theorem relative_box_adjacent {p : Nat} (q r : Pose p) (j : Fin p)
    (haxis : boxLower r j = boxLower q j + 2 ∨ boxLower q j = boxLower r j + 2)
    (htrans : ∀ i, i ≠ j → boxLower q i = boxLower r i) :
    ∃ side, boxLower (q.relative r) = wallBox (q.frame.perm j) side := by
  rcases haxis with haxis | haxis
  · refine ⟨!(q.frame.negative j), ?_⟩
    funext i
    rw [relative_boxLower]
    by_cases hi : i = q.frame.perm j
    · subst i
      rw [q.frame.left_inverse, haxis]
      cases hn : q.frame.negative j <;> simp [wallBox, RegisteredFrame.sign, hn] <;> omega
    · have hn : q.frame.inverse i ≠ j := by
        intro he
        apply hi
        exact (q.frame.right_inverse i).symm.trans (congrArg q.frame.perm he)
      rw [htrans _ hn]
      simp [wallBox, hi]
  · refine ⟨q.frame.negative j, ?_⟩
    funext i
    rw [relative_boxLower]
    by_cases hi : i = q.frame.perm j
    · subst i
      rw [q.frame.left_inverse, haxis]
      cases hn : q.frame.negative j <;> simp [wallBox, RegisteredFrame.sign, hn] <;> omega
    · have hn : q.frame.inverse i ≠ j := by
        intro he
        apply hi
        exact (q.frame.right_inverse i).symm.trans (congrArg q.frame.perm he)
      rw [htrans _ hn]
      simp [wallBox, hi]
theorem relative_mask_at_axis {p : Nat} (q r : Pose p) (j : Fin p) (color : Bool)
    (hmask : ∀ i, xor (q.frame.negative i) (r.frame.negative i) =
      if i = j then !color else color) :
    ∀ i, (q.relative r).frame.negative i = if i = q.frame.perm j then !color else color := by
  intro i
  rw [relative_negative, hmask]
  by_cases hi : i = q.frame.perm j
  · subst i
    simp [q.frame.left_inverse]
  · have hn : q.frame.inverse i ≠ j := by
      intro he
      apply hi
      exact (q.frame.right_inverse i).symm.trans (congrArg q.frame.perm he)
    simp [hi, hn]
theorem colored_contact_wall_geometry {p : Nat} (hp : 3 ≤ p) (q r : Pose p)
    (hq : CarrierColored q) (hr : CarrierColored r) (hc : FaceContact q r)
    (he : ∀ i, (q.relative r).anchor i % 2 = 0) : WallGeometry (q.relative r) := by
  obtain ⟨j, hj, ht, color, hmask⟩ := colored_contact_mask hp q r hq hr hc
    (even_relative_box_parity q r he)
  obtain ⟨side, hs⟩ := relative_box_adjacent q r j hj ht
  exact wall_geometry_of_box_mask _ _ side color hs (relative_mask_at_axis q r j color hmask)
theorem Pose.Same.hole {p : Nat} {q r : Pose p} (h : q.Same r) :
    RegisteredPrime.hole q = RegisteredPrime.hole r := h.cell (fun _ => 1)
theorem Pose.Same.wall_geometry {p : Nat} {q r : Pose p} (h : q.Same r)
    (hq : WallGeometry q) : WallGeometry r := by
  obtain ⟨j, hq | hq⟩ := hq
  · exact ⟨j, Or.inl ⟨h.boxLower.symm.trans hq.1,
      hq.2.elim (fun hh => Or.inl (h.hole.symm.trans hh))
        (fun hh => Or.inr (h.hole.symm.trans hh))⟩⟩
  · exact ⟨j, Or.inr ⟨h.boxLower.symm.trans hq.1,
      hq.2.elim (fun hh => Or.inl (h.hole.symm.trans hh))
        (fun hh => Or.inr (h.hole.symm.trans hh))⟩⟩
theorem generated_wall_property (P : Parameters) : GeneratedWallProperty P := by
  intro e he heven
  obtain ⟨n, q, r, hq, hr, hc, hs⟩ := he
  have heven' : ∀ i, (q.relative r).anchor i % 2 = 0 := by
    intro i
    rw [hs.2.2 i]
    exact heven i
  exact hs.wall_geometry (colored_contact_wall_geometry (P.prime.three_le P.odd) q r
    (generated_tile_carrier_colored P n q hq) (generated_tile_carrier_colored P n r hr) hc heven')
theorem registered_support_fan_unconditional (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (hroot : W.tiles (identityPose P.p)) {A : Mask P.p}
    (hA : Proper A) (hnA : NonemptyMask A)
    (hin : (normalizedLocalPatch P W hl hroot (generated_wall_property P)).incoming A) :
    ∀ B, Proper B →
      (normalizedLocalPatch P W hl hroot (generated_wall_property P)).incoming B :=
  registered_support_fan P W hl hroot (generated_wall_property P) hA hnA hin
end RegisteredPrime
