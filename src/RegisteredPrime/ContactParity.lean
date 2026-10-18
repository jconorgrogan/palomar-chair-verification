module
public import RegisteredPrime.FrameBridge
@[expose] public section
namespace RegisteredPrime
def Pose.UniformParity {p : Nat} (q : Pose p) : Prop :=
  ∃ b : Bool, ∀ i, q.anchor i % 2 = bit b
def centralBit {p : Nat} : Role p → Bool
  | .central => true
  | .outer _ _ => false
theorem refine_anchor_parity (P : Parameters) (q : Pose P.p) (r : Role P.p) :
    ∀ i, (refine P q r).anchor i % 2 = bit (centralBit r) := by
  intro i
  cases r with
  | central =>
    simp only [refine, Pose.comp, RegisteredFrame.linear, RegisteredFrame.sign,
      arithmeticChild, childShift, centralBit, bit]
    by_cases h : q.frame.negative i = true <;> simp [h] <;> omega
  | outer A hp =>
    simp only [refine, Pose.comp, RegisteredFrame.linear, RegisteredFrame.sign,
      arithmeticChild, childShift, centralBit, bit]
    by_cases hn : q.frame.negative i = true <;>
      by_cases ha : A (q.frame.perm i) = true <;> simp [hn, ha] <;> omega
theorem refine_uniform_parity (P : Parameters) (q : Pose P.p) (r : Role P.p) :
    (refine P q r).UniformParity := ⟨centralBit r, refine_anchor_parity P q r⟩
theorem Pose.Same.uniform_parity {p : Nat} {q r : Pose p} (h : q.Same r)
    (hq : q.UniformParity) : r.UniformParity := by
  obtain ⟨b, hb⟩ := hq
  exact ⟨b, fun i => by rw [← h.2.2 i]; exact hb i⟩
theorem descendant_uniform_parity (P : Parameters) (n : Nat) (q t : Pose P.p)
    (hq : q.UniformParity) (ht : Descendant P n q t) : t.UniformParity := by
  induction n generalizing q with
  | zero => exact Pose.Same.uniform_parity ht hq
  | succ n ih =>
    obtain ⟨r, hr⟩ := ht
    exact ih (refine P q r) (refine_uniform_parity P q r) hr
theorem Pose.uniform_parity_relative {p : Nat} (q r : Pose p)
    (hq : q.UniformParity) (hr : r.UniformParity) : (q.relative r).UniformParity := by
  obtain ⟨b, hb⟩ := hq
  obtain ⟨c, hc⟩ := hr
  refine ⟨xor b c, fun i => ?_⟩
  have h1 := hb (q.frame.inverse i)
  have h2 := hc (q.frame.inverse i)
  simp only [Pose.relative, Pose.comp, Pose.inv, RegisteredFrame.linear,
    RegisteredFrame.inv, RegisteredFrame.sign]
  cases b <;> cases c <;> by_cases hn : q.frame.negative (q.frame.inverse i) = true <;>
    simp [hn, bit] at h1 h2 ⊢ <;> omega
theorem generated_contact_constant_parity (P : Parameters) (e : Pose P.p)
    (he : GeneratedContact P e) : e.UniformParity := by
  obtain ⟨n, q, r, hq, hr, _, he⟩ := he
  have hroot : (identityPose P.p).UniformParity := ⟨false, fun _ => rfl⟩
  exact he.uniform_parity (q.uniform_parity_relative r
    (descendant_uniform_parity P n _ _ hroot hq)
    (descendant_uniform_parity P n _ _ hroot hr))
theorem legal_contact_constant_parity (P : Parameters) (W : RegisteredWorld P.p)
    (hW : W.Legal P) (q r : Pose P.p) (hq : W.tiles q) (hr : W.tiles r)
    (hc : FaceContact q r) : (q.relative r).UniformParity :=
  generated_contact_constant_parity P _ (hW q r hq hr hc)
end RegisteredPrime
