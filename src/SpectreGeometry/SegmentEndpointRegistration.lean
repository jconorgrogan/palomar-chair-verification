module

public import SpectreGeometry.NoVertexInEdge

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

theorem segment_endpoint_registration (A B C D x : EPlane) (t u : ℝ)
    (ht : 0 < t) (ht' : t < 1) (hu : 0 < u) (hu' : u < 1)
    (hx : x = A + t • (B-A)) (hy : x = C + u • (D-C))
    (hv : B-A = D-C ∨ B-A = -(D-C))
    (hnAC : ∀ s : ℝ, 0 < s → s < 1 → A+s • (B-A) ≠ C)
    (hnAD : ∀ s : ℝ, 0 < s → s < 1 → A+s • (B-A) ≠ D)
    (hnCA : ∀ s : ℝ, 0 < s → s < 1 → C+s • (D-C) ≠ A) :
    (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  rcases hv with hv | hv
  · have hC : C = A+(t-u) • (B-A) := by
      calc
        C = (C+u • (D-C))-u • (D-C) := by abel
        _ = (A+t • (B-A))-u • (B-A) := by rw [←hy,hx,←hv]
        _ = A+(t-u) • (B-A) := by rw [sub_smul]; abel
    have hA : A = C+(u-t) • (D-C) := by
      calc
        A = (A+t • (B-A))-t • (B-A) := by abel
        _ = (C+u • (D-C))-t • (D-C) := by rw [←hx,hy,hv]
        _ = C+(u-t) • (D-C) := by rw [sub_smul]; abel
    have htu : t = u := by
      rcases lt_trichotomy t u with h | h | h
      · exact False.elim (hnCA (u-t) (by linarith) (by linarith) hA.symm)
      · exact h
      · exact False.elim (hnAC (t-u) (by linarith) (by linarith) hC.symm)
    have hAC : A = C := by simpa [htu] using hC.symm
    exact Or.inl ⟨hAC,by rw [hAC] at hv; exact sub_left_injective hv⟩
  · have hw : D-C = -(B-A) := by rw [hv,neg_neg]
    have hC : C = A+(t+u) • (B-A) := by
      calc
        C = (C+u • (D-C))-u • (D-C) := by abel
        _ = (A+t • (B-A))-u • (-(B-A)) := by rw [←hy,hx,hw]
        _ = A+(t+u) • (B-A) := by rw [add_smul,smul_neg]; abel
    have hD : D = A+(t+u-1) • (B-A) := by
      calc
        D = C+(D-C) := by abel
        _ = (A+(t+u) • (B-A)) + (-(B-A)) := by rw [hw,hC]
        _ = A+(t+u-1) • (B-A) := by rw [sub_smul,one_smul]; abel
    have hsum : t+u = 1 := by
      rcases lt_trichotomy (t+u) 1 with h | h | h
      · exact False.elim (hnAC (t+u) (by linarith) h hC.symm)
      · exact h
      · exact False.elim (hnAD (t+u-1) (by linarith) (by linarith) hD.symm)
    have hAD : A = D := by simpa [hsum] using hD.symm
    have hBC : B = C := by simpa [hsum] using hC.symm
    exact Or.inr ⟨hAD,hBC⟩

end
end SpectreGeometry
