module
public import RegisteredPrime.HoleOwnerRecursion
@[expose] public section
namespace RegisteredPrime
theorem hole_owner_box_position {p : Nat} (hp : 3 ≤ p) (q r : Pose p)
    (hqu : q.UniformParity) (hru : r.UniformParity) (hd : Disjoint q r)
    (hown : Occupies r (hole q)) :
    ∀ i, boxLower r i = boxLower q i + 1 - 2 * bit (q.frame.negative i) := by
  obtain ⟨b, hb⟩ := hqu
  obtain ⟨c, hc⟩ := hru
  have hqb := uniform_parity_box q b hb
  have hrb := uniform_parity_box r c hc
  have hbox := (occupies_box_iff r (hole q)).mp hown
  have hbc : b ≠ c := by
    intro he
    have hsame : boxLower q = boxLower r := by
      funext i
      have h1 := hqb i
      have h2 := hrb i
      have h3 := hbox.1 i
      rw [hole_from_box] at h3
      rw [he] at h1
      cases c <;> cases hn : q.frame.negative i <;> simp [bit, hn] at h1 h2 h3 <;> omega
    have h01 : (⟨0, by omega⟩ : Fin p) ≠ ⟨1, by omega⟩ := by
      intro h
      have hv := congrArg Fin.val h
      change (0 : Nat) = 1 at hv
      omega
    obtain ⟨x, hqx, hrx⟩ := same_box_overlap q r ⟨0, by omega⟩ ⟨1, by omega⟩ h01 hsame
    exact hd x ⟨hqx, hrx⟩
  intro i
  have h1 := hqb i
  have h2 := hrb i
  have h3 := hbox.1 i
  rw [hole_from_box] at h3
  cases b <;> cases c <;> cases hn : q.frame.negative i <;>
    simp [bit, hn] at hbc h1 h2 h3 ⊢ <;> omega
theorem central_child_not_hole_owner (P : Parameters) (q r : Pose P.p)
    (hqu : q.UniformParity) (hru : r.UniformParity) (hd : Disjoint q r)
    (hown : Occupies r (hole q)) :
    ¬ Occupies (refine P r .central) (hole (refine P q .central)) := by
  intro hf
  have hp := P.prime.three_le P.odd
  let i : Fin P.p := ⟨0, by omega⟩
  have h := ((occupies_box_iff _ _).mp hf).1 i
  have he := hole_owner_box_position hp q r hqu hru hd hown i
  rw [hole_from_box, refine_central_lower, refine_central_negative,
    refine_central_lower, he] at h
  cases hn : q.frame.negative i <;> simp [bit, hn] at h <;> omega
theorem central_leaf_owner_is_outer (P : Parameters) (n : Nat) (q r : Pose P.p)
    (hq : Descendant P n (identityPose P.p) q)
    (hr : Descendant P n (identityPose P.p) r) (a : Role P.p)
    (hf : Occupies (refine P r a) (hole (refine P q .central))) :
    ∃ A, ∃ hA : Proper A, a = Role.outer A hA := by
  cases a with
  | outer A hA => exact ⟨A, hA, rfl⟩
  | central =>
    have hown := central_leaf_owner_parent P q r .central hf
    have hroot : (identityPose P.p).UniformParity := ⟨false, fun _ => rfl⟩
    exact False.elim (central_child_not_hole_owner P q r
      (descendant_uniform_parity P n _ q hroot hq)
      (descendant_uniform_parity P n _ r hroot hr)
      (descendant_hole_owner_disjoint P n _ q r hq hr hown) hown hf)
theorem refine_outer_macrocell (P : Parameters) (r : Pose P.p) (A : Mask P.p)
    (hA : Proper A) (i : Fin P.p) :
    boxLower (refine P r (.outer A hA)) i = 2 * r.cell (fun j => bit (A j)) i := by
  rw [refine_outer_lower, refine_outer_negative]
  simp only [boxLower, Pose.cell, RegisteredFrame.linear, RegisteredFrame.sign, bit]
  by_cases hn : r.frame.negative i = true <;>
    by_cases ha : A (r.frame.perm i) = true <;> simp [hn, ha] <;> omega
theorem outer_owner_role_cell (P : Parameters) (r : Pose P.p) (A : Mask P.p)
    (hA : Proper A) (c : Cell P.p) (hc : Occupies (refine P r (.outer A hA)) c) :
    r.cell (fun j => bit (A j)) = floorCell c := by
  funext i
  have h := ((occupies_box_iff _ _).mp hc).1 i
  rw [refine_outer_macrocell] at h
  simp only [floorCell]
  omega
theorem central_owner_source_role (P : Parameters) (q r : Pose P.p) (A : Mask P.p)
    (hA : Proper A) (hc : Occupies (refine P r (.outer A hA)) (hole (refine P q .central))) :
    (fun j => bit (A j)) = r.inv.cell (hole q) := by
  have he := outer_owner_role_cell P r A hA _ hc
  rw [central_hole_floor] at he
  have h := congrArg r.inv.cell he
  simpa using h
end RegisteredPrime
