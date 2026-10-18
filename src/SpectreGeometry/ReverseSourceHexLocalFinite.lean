module

public import SpectreGeometry.ReverseSourceHexCover

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set

theorem sourceHex_coordinate_bounds {c : ℤ × ℤ} {p : ℝ × ℝ}
    (h : p ∈ sourceHexCarrier c) :
    |p.1-c.1| ≤ 1 ∧ |p.2-c.2| ≤ 1 := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem sourceHex_isClosed (c : ℤ × ℤ) : IsClosed (sourceHexCarrier c) := by
  have h1 : Continuous (fun p : ℝ × ℝ => 2*(p.1-c.1)+(p.2-c.2)) := by fun_prop
  have h2 : Continuous (fun p : ℝ × ℝ => (p.1-c.1)+2*(p.2-c.2)) := by fun_prop
  have h3 : Continuous (fun p : ℝ × ℝ => (p.1-c.1)-(p.2-c.2)) := by fun_prop
  exact (isClosed_le continuous_const h1).inter
    ((isClosed_le h1 continuous_const).inter
      ((isClosed_le continuous_const h2).inter
        ((isClosed_le h2 continuous_const).inter
          ((isClosed_le continuous_const h3).inter (isClosed_le h3 continuous_const)))))

theorem sourceHex_locallyFinite : LocallyFinite sourceHexCarrier := by
  intro x
  refine ⟨Ioo (x.1-1) (x.1+1) ×ˢ Ioo (x.2-1) (x.2+1), ?_, ?_⟩
  · apply (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  · apply (Set.finite_Icc (⌊x.1⌋-3,⌊x.2⌋-3) (⌊x.1⌋+3,⌊x.2⌋+3)).subset
    rintro c ⟨y,hy,hyx⟩
    obtain ⟨hb1,hb2⟩ := sourceHex_coordinate_bounds hy
    rw [abs_le] at hb1 hb2
    have hxl := Int.floor_le x.1
    have hxu := Int.lt_floor_add_one x.1
    have hyl := Int.floor_le x.2
    have hyu := Int.lt_floor_add_one x.2
    have hl1 : ((⌊x.1⌋-3 : ℤ) : ℝ) ≤ c.1 := by push_cast; linarith [hyx.1.1]
    have hl2 : ((⌊x.2⌋-3 : ℤ) : ℝ) ≤ c.2 := by push_cast; linarith [hyx.2.1]
    have hu1 : (c.1 : ℝ) ≤ ((⌊x.1⌋+3 : ℤ) : ℝ) := by push_cast; linarith [hyx.1.2]
    have hu2 : (c.2 : ℝ) ≤ ((⌊x.2⌋+3 : ℤ) : ℝ) := by push_cast; linarith [hyx.2.2]
    exact ⟨⟨by exact_mod_cast hl1,by exact_mod_cast hl2⟩,
      ⟨by exact_mod_cast hu1,by exact_mod_cast hu2⟩⟩

end
end SpectreGeometry.ReverseExistence
