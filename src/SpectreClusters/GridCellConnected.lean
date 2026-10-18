module

public import SpectreClusters.GridNeighborTransport

@[expose] public section


/-! The entire kite contact graph is connected, without a physical-plane
assumption or a supplied graph-connectivity hypothesis. -/
namespace SpectreClusters

theorem cellContact_origin_sectors : ∀ a b : Turn,
    CellContact ⟨(0,0),a⟩ ⟨(0,0),b⟩ := by decide

theorem cellContact_step_q : CellContact ⟨(0,0),0⟩ ⟨(1,0),2⟩ := by decide

theorem cellContact_step_r : CellContact ⟨(0,0),0⟩ ⟨(0,1),3⟩ := by decide

theorem cellContact_same_center (t : Point) (a b : Turn) :
    CellContact ⟨t,a⟩ ⟨t,b⟩ := by
  have h := cellContact_moved 0 t _ _ (cellContact_origin_sectors a b)
  simpa [moveCell,translateCell,rotateCell,rotate,turnAdd_zero,add] using h

theorem cellContact_step_q_at (q r : Int) :
    CellContact ⟨(q,r),0⟩ ⟨(q+1,r),2⟩ := by
  have h := cellContact_moved 0 (q,r) _ _ cellContact_step_q
  simpa [moveCell,translateCell,rotateCell,rotate,turnAdd_zero,add] using h

theorem cellContact_step_r_at (q r : Int) :
    CellContact ⟨(q,r),0⟩ ⟨(q,r+1),3⟩ := by
  have h := cellContact_moved 0 (q,r) _ _ cellContact_step_r
  simpa [moveCell,translateCell,rotateCell,rotate,turnAdd_zero,add] using h

theorem int_step_function_constant {α : Sort u} (g : Int → α)
    (h : ∀ z, g (z+1) = g z) (z : Int) : g z = g 0 := by
  cases z with
  | ofNat n =>
    induction n with
    | zero => rfl
    | succ n ih =>
      have he : (Int.ofNat (n+1)) = Int.ofNat n + 1 := by rfl
      rw [he,h]
      exact ih
  | negSucc n =>
    induction n with
    | zero =>
      have hz := h (-1)
      exact hz.symm
    | succ n ih =>
      have hz := h (Int.negSucc (n+1))
      have he : Int.negSucc (n+1) + 1 = Int.negSucc n := by omega
      rw [he] at hz
      exact hz.symm.trans ih

/-- Any invariant of contacting cells has the same value everywhere. -/
theorem contact_invariant_constant {α : Sort u} (g : Cell → α)
    (h : ∀ a b, CellContact a b → g a = g b) (a b : Cell) : g a = g b := by
  have hq (q r : Int) : g ⟨(q+1,r),0⟩ = g ⟨(q,r),0⟩ := by
    exact (h _ _ (cellContact_same_center (q+1,r) 0 2)).trans
      (h _ _ (cellContact_step_q_at q r)).symm
  have hr (r : Int) : g ⟨(0,r+1),0⟩ = g ⟨(0,r),0⟩ := by
    exact (h _ _ (cellContact_same_center (0,r+1) 0 3)).trans
      (h _ _ (cellContact_step_r_at 0 r)).symm
  have he (c : Cell) : g c = g ⟨(0,0),0⟩ := by
    have hs := h _ _ (cellContact_same_center c.center c.sector 0)
    have hx := int_step_function_constant (fun q => g ⟨(q,c.center.2),0⟩)
      (fun q => hq q c.center.2) c.center.1
    have hy := int_step_function_constant (fun r => g ⟨(0,r),0⟩) hr c.center.2
    exact hs.trans (hx.trans hy)
  exact (he a).trans (he b).symm

end SpectreClusters
