module

public import ProductClosure.GlobalRegistration
public import ProductClosure.NativeProfileDefinitions

@[expose] public section

/-! Exact full-profile equations for actual physical tilings. Whole companions
and retained cell cores identify the unique carrier owner across each paired
site; no contact-law assumption is made. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

theorem placed_cellCenter_mem_interior_body
    {J : ℕ} [NeZero m] (a : Coefficients polyCells J)
    (f : Space m ≃ᵢ Space m) (c : Polycube.Cell polyCells) :
    f (cellCenter c) ∈ interior (placedBody a f) := by
  apply f.toHomeomorph.isOpenMap.image_interior_subset (body a)
  exact ⟨cellCenter c, cellCenter_ball_subset_interior_body a c
    (Metric.mem_ball_self (by norm_num)), rfl⟩

/-- Distinct actual physical tiles cannot own the same placed cell center,
because each center lies in an actual retained interior ball. -/
theorem PhysicalTiling.cellCenter_owner_unique
    {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {i j : ι} (c d : Polycube.Cell polyCells)
    (h : f i (cellCenter c) = f j (cellCenter d)) : i = j := by
  by_contra hij
  have hi := placed_cellCenter_mem_interior_body a (f i) c
  have hj := placed_cellCenter_mem_interior_body a (f j) d
  rw [← h] at hj
  exact Set.disjoint_left.mp (T.interiors_disjoint hij) hi hj

theorem PhysicalTiling.relative_cellCenter_owner_unique
    {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) {i j : ι} (c d : Polycube.Cell polyCells)
    (h : relativePlacement (f root) (f i) (cellCenter c) =
      relativePlacement (f root) (f j) (cellCenter d)) : i = j := by
  apply T.cellCenter_owner_unique c d
  have hh := congrArg (f root) h
  simpa [relativePlacement] using hh

/-- Geometric site transport in relative coordinates gives the actual
world-frame tangent, normal and center equations. -/
theorem SiteTransport.relative_world_frame 
    (f g : Space m ≃ᵢ Space m) (u v : Site polyCells)
    (h : SiteTransport (relativePlacement f g) u v) :
    (∀ j, placedNormal g (siteAxis v j) = placedNormal f (siteAxis u j)) ∧
    placedNormal g (outward v.1) = -placedNormal f (outward u.1) ∧
    f (siteCenter u) = g (siteCenter v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hh := congrArg (placedNormal f) (h.1 j)
    rwa [placedNormal_relative] at hh
  · have hh := congrArg (placedNormal f) h.2.1
    rw [placedNormal_relative] at hh
    simpa [placedNormal] using hh
  · have hh := congrArg f h.2.2
    simpa [relativePlacement] using hh.symm

/-- Every paired site of every actual pair has opposite coefficients. The
proof identifies the supplied mate with the actual unique whole companion;
neither its profile equation nor carrier contact legality is assumed. -/
theorem PhysicalTiling.paired_site_coefficients_opposite
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (i j : ι) (u v : Site polyCells)
    (h : SiteTransport (relativePlacement (f i) (f j)) u v) :
    a.value v = -a.value u := by
  obtain ⟨ht, hn, hc⟩ := h.relative_world_frame (f i) (f j) u v
  obtain ⟨iv, hiv, _⟩ := T.unique_framed_key_companion hm i u
  have hvcell := matched_companion_cellCenter u v (f i) (f j) ht hn hc
  have hivcell := matched_companion_cellCenter u iv.2 (f i) (f iv.1)
    hiv.2.2.1 hiv.2.2.2.1 hiv.2.2.2.2.1
  have hj : j = iv.1 := T.cellCenter_owner_unique (facetInsideCell v.1)
    (facetInsideCell iv.2.1) (hvcell.trans hivcell.symm)
  have hv : v = iv.2 := by
    apply siteCenter_injective hm
    apply (f j).injective
    have hiCenter := hiv.2.2.2.2.1
    rw [← hj] at hiCenter
    exact hc.symm.trans hiCenter
  rw [hv]
  exact hiv.2.2.2.2.2

theorem PhysicalTiling.full_profile_mating
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (i j : ι) :
    FullProfileMating a (relativePlacement (f i) (f j)) :=
  T.paired_site_coefficients_opposite hm i j

/-- For the constructed contact-graph coefficients, every geometrically
paired site in an actual physical tiling lies in its generating component. -/
theorem PhysicalTiling.compiled_paired_sites_connected
     [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling (compiledCoefficients (S := polyCells) hm A hA) f)
    (i j : ι) (u v : Site polyCells)
    (h : SiteTransport (relativePlacement (f i) (f j)) u v) :
    (contactGraph A hA).Reachable u v := by
  letI := nativeSiteOrder (S := polyCells) hm
  exact ((graphCoefficients_opposite_iff (contactGraph A hA) u v).mp
    (T.paired_site_coefficients_opposite hm i j u v h)).1

end
end ProductClosure.NativeCompiler
