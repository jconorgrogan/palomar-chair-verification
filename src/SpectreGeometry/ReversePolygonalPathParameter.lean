module

public import SpectreGeometry.ReverseUnitSubdivision

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set

def PathParameter (ps : List (ℝ × ℝ)) (t : ℝ) (y : ℝ × ℝ) : Prop :=
  ∃ j : Nat, j < ps.length - 1 ∧ ∃ u ∈ Icc (0:ℝ) 1,
    t = ((j:ℝ) + u) / (ps.length - 1 : Nat) ∧
    y = AffineMap.lineMap (ps.getD j 0) (ps.getD (j+1) 0) u

private theorem uniform_parameter_unique_or_endpoint (n j k : Nat) (hn : 0 < n)
    (u v : ℝ) (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1)
    (he : ((j:ℝ)+u)/n = ((k:ℝ)+v)/n) :
    (j = k ∧ u = v) ∨ (j+1 = k ∧ u = 1 ∧ v = 0) ∨
      (k+1 = j ∧ v = 1 ∧ u = 0) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsum : (j:ℝ)+u = (k:ℝ)+v := (div_left_inj' hnR).mp he
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · have hle : (j:ℝ)+1 ≤ k := by exact_mod_cast hjk
    have heq : (j:ℝ)+1 = k := by linarith [hu.1,hu.2,hv.1,hv.2]
    right; left
    exact ⟨by exact_mod_cast heq, by linarith [hu.2,hv.1], by linarith [hu.2,hv.1]⟩
  · left
    exact ⟨hjk,by subst k; linarith⟩
  · have hle : (k:ℝ)+1 ≤ j := by exact_mod_cast hjk
    have heq : (k:ℝ)+1 = j := by linarith [hu.1,hu.2,hv.1,hv.2]
    right; right
    exact ⟨by exact_mod_cast heq,by linarith [hu.1,hv.2],by linarith [hu.1,hv.2]⟩

theorem PathParameter.unique {ps : List (ℝ × ℝ)} {t : ℝ} {y z : ℝ × ℝ}
    (hy : PathParameter ps t y) (hz : PathParameter ps t z) : y = z := by
  obtain ⟨j,hj,u,hu,ht,hy⟩ := hy
  obtain ⟨k,hk,v,hv,hs,hz⟩ := hz
  have hn : 0 < ps.length-1 := by omega
  rcases uniform_parameter_unique_or_endpoint (ps.length-1) j k hn u v hu hv
      (ht.symm.trans hs) with ⟨rfl,rfl⟩ | ⟨hjk,rfl,rfl⟩ | ⟨hkj,rfl,rfl⟩
  · exact hy.trans hz.symm
  · rw [hy,hz]; simp [hjk]
  · rw [hy,hz]; simp [hkj]

theorem PathParameter.exists (ps : List (ℝ × ℝ)) (hn : 2 ≤ ps.length)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ∃ y, PathParameter ps t y := by
  obtain ⟨j,u,hu,he⟩ := unit_subdivision (ps.length-1) (by omega) t ht
  exact ⟨_,j.val,j.isLt,u,hu,he,rfl⟩

end
end SpectreGeometry.ReverseExistence
