module

public import ProductClosure.MaterialCovariance
public import PhysicalRegistration.NativeMaterialGluing

@[expose] public section

namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration
open PhysicalRegistration.NativeMaterialGluing
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}

/-- Isometric placement commutes with the literal finite tube assembly. -/
theorem placedBody_eq_assemble {J : ℕ} [NeZero m]
    (a : Coefficients polyCells J) (f : Space m ≃ᵢ Space m) :
    placedBody a f = assemble (f '' Polycube.carrier polyCells)
      (fun u => f '' closedTube J u) (fun u => f '' replacementPiece a u) := by
  unfold placedBody body assemble
  rw [Set.image_union, Set.image_sdiff f.injective, Set.image_iUnion, Set.image_iUnion]
  have hi (u : Site polyCells) : f '' interior (closedTube J u) = interior (f '' closedTube J u) :=
    f.toHomeomorph.image_interior _
  simp_rw [hi]


/-- Relative-coordinate images bind exactly to the two original placements. -/
theorem placed_relative_image  (f g : Space m ≃ᵢ Space m) (S : Set (Space m)) :
    f '' (relativePlacement f g '' S) = g '' S := by
  rw [Set.image_image]
  have he : (fun x => f (relativePlacement f g x)) = g := by
    funext x
    exact f.apply_symm_apply (g x)
  rw [he]

/-- A matched native site pair has one literal common world-coordinate tube. -/
theorem SiteTransport.placed_closedTube 
    {f g : Space m ≃ᵢ Space m} {u v : Site polyCells}
    (h : SiteTransport (relativePlacement f g) u v) (J : ℕ) :
    f '' closedTube J u = g '' closedTube J v := by
  have hp := congrArg (Set.image f) (h.image_closedTube J)
  rw [placed_relative_image] at hp
  exact hp.symm

/-- Actual paired material pieces cover their common tube in world coordinates. -/
theorem SiteTransport.placed_replacementPiece_union {J : ℕ} [NeZero m]
    {f g : Space m ≃ᵢ Space m} {u v : Site polyCells}
    (h : SiteTransport (relativePlacement f g) u v)
    (a : Coefficients polyCells J) (hc : a.value v = -a.value u) :
    (f '' replacementPiece a u) ∪ (g '' replacementPiece a v) = f '' closedTube J u := by
  have hp := congrArg (Set.image f) (h.replacementPiece_union a hc)
  rw [Set.image_union, placed_relative_image] at hp
  exact hp

/-- Their actual world-coordinate interiors remain disjoint under placement. -/
theorem SiteTransport.placed_replacementPiece_interiors_disjoint
    {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    {f g : Space m ≃ᵢ Space m} {u v : Site polyCells}
    (h : SiteTransport (relativePlacement f g) u v)
    (a : Coefficients polyCells J) (hc : a.value v = -a.value u) :
    Disjoint (interior (f '' replacementPiece a u)) (interior (g '' replacementPiece a v)) := by
  have hd := (Set.disjoint_image_iff f.injective).mpr
    (h.replacementPiece_interiors_disjoint hm a hc)
  have hi (S : Set (Space m)) : f '' interior S = interior (f '' S) :=
    f.toHomeomorph.image_interior S
  rw [hi, hi, placed_relative_image] at hd
  exact hd

/-- Actual placed body coverage and nonoverlap follow from the carrier world,
paired tube geometry, and local complementary replacement pieces. -/
theorem physicalTiling_of_tube_partitions
    {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients polyCells J) (f : ι → Space m ≃ᵢ Space m)
    (hcover : ∀ x, ∃ i, x ∈ f i '' Polycube.carrier polyCells)
    (hcarrier : Pairwise fun i j =>
      Disjoint (interior (f i '' Polycube.carrier polyCells)) (interior (f j '' Polycube.carrier polyCells)))
    (hfill : ∀ i u, ∃ j v, f i '' closedTube J u ⊆
      (f i '' replacementPiece a u) ∪ (f j '' replacementPiece a v))
    (hisolation : ∀ i j, i ≠ j → ∀ u : Site polyCells,
      Disjoint (f i '' closedTube J u) (f j '' Polycube.carrier polyCells) ∨
        ∃ v : Site polyCells, f i '' closedTube J u = f j '' closedTube J v)
    (hpieces : ∀ i j, i ≠ j → ∀ u v,
      Disjoint (f i '' closedTube J u) (f j '' closedTube J v) ∨
        Disjoint (interior (f i '' replacementPiece a u))
          (interior (f j '' replacementPiece a v))) : PhysicalTiling a f := by
  have hCclosed (i : ι) : IsClosed (f i '' Polycube.carrier polyCells) :=
    (f i).toHomeomorph.isClosedMap _ (carrier_isClosed polyCells)
  have hPclosed (i : ι) (u : Site polyCells) : IsClosed (f i '' replacementPiece a u) :=
    (f i).toHomeomorph.isClosedMap _ ((closedTube_isClosed J u).inter (siteHypograph_isClosed a u))
  have hPsub (i : ι) (u : Site polyCells) : f i '' replacementPiece a u ⊆ f i '' closedTube J u :=
    Set.image_mono inter_subset_left
  constructor
  · simpa only [placedBody_eq_assemble] using assemble_interiors_disjoint
      (fun i => f i '' Polycube.carrier polyCells) (fun i u => f i '' closedTube J u)
      (fun i u => f i '' replacementPiece a u) hCclosed hPclosed hPsub hcarrier hisolation hpieces
  · simpa only [placedBody_eq_assemble] using assemble_covers
      (fun i => f i '' Polycube.carrier polyCells) (fun i u => f i '' closedTube J u)
      (fun i u => f i '' replacementPiece a u) hcover hfill


/-- A geometric matched-tube interface: every tube is paired, and distinct
world tubes either miss or arise from an actual complete native site matching
with opposite coefficients. The material gluing conclusion is derived. -/
theorem physicalTiling_of_matched_tubes
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (a : Coefficients polyCells J) (f : ι → Space m ≃ᵢ Space m)
    (hcover : ∀ x, ∃ i, x ∈ f i '' Polycube.carrier polyCells)
    (hcarrier : Pairwise fun i j =>
      Disjoint (interior (f i '' Polycube.carrier polyCells)) (interior (f j '' Polycube.carrier polyCells)))
    (hmatch : ∀ i u, ∃ j v, SiteTransport (relativePlacement (f i) (f j)) u v ∧
      a.value v = -a.value u)
    (hisolation : ∀ i j, i ≠ j → ∀ u : Site polyCells,
      Disjoint (f i '' closedTube J u) (f j '' Polycube.carrier polyCells) ∨
        ∃ v : Site polyCells, f i '' closedTube J u = f j '' closedTube J v)
    (htubes : ∀ i j, i ≠ j → ∀ u v,
      Disjoint (f i '' closedTube J u) (f j '' closedTube J v) ∨
        (SiteTransport (relativePlacement (f i) (f j)) u v ∧ a.value v = -a.value u)) :
    PhysicalTiling a f := by
  apply physicalTiling_of_tube_partitions a f hcover hcarrier
  · intro i u
    obtain ⟨j, v, ht, hc⟩ := hmatch i u
    exact ⟨j, v, (ht.placed_replacementPiece_union a hc).symm.subset⟩
  · exact hisolation
  · intro i j hij u v
    rcases htubes i j hij u v with hd | ⟨ht, hc⟩
    · exact Or.inl hd
    · exact Or.inr (ht.placed_replacementPiece_interiors_disjoint hm a hc)

#print axioms placedBody_eq_assemble
#print axioms SiteTransport.placed_replacementPiece_union
#print axioms SiteTransport.placed_replacementPiece_interiors_disjoint
#print axioms physicalTiling_of_matched_tubes
#print axioms physicalTiling_of_tube_partitions
end
end ProductClosure.NativeCompiler
