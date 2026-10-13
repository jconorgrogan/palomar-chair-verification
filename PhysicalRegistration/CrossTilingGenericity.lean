module

public import PhysicalRegistration.GenericAffineAvoidance
public import PhysicalRegistration.PackingLocalFiniteness
public import PhysicalRegistration.NativeBoundaryPlanes

@[expose] public section

/-!
# Dense native crease points generic across arbitrary placed neighbors

An arbitrary interior-disjoint isometric packing has finitely many neighbors
of any fixed body. Among their literal finite native boundary planes, remove
precisely those that do not contain the entire selected placed crease.
Convexity supplies density after these deletions. Consequently every remaining
point lies only on neighboring planes that contain its whole crease. Neither
coverage, an assumed contact theorem, nor supplied plane-properness witnesses
are required.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

/-- Finite affine planes can always be sorted into planes containing `C` and
planes avoidable on a dense subset of its already dense generic part. The
noncontainment witnesses are derived from the finite filter itself. -/
theorem convex_generic_finite_plane_dichotomy {m : ℕ} {κ : Type*} [Fintype κ]
    (C G : Set (Space m)) (hC : Convex ℝ C) (hClosed : IsClosed C)
    (hG : closure G = C) (n : κ → Space m) (c : κ → ℝ) :
    ∃ D : Set (Space m), D ⊆ G ∧ closure D = C ∧
      ∀ x ∈ D, ∀ k, ⟪n k, x⟫_ℝ = c k → C ⊆ {y | ⟪n k, y⟫_ℝ = c k} := by
  classical
  let I : Finset κ := Finset.univ.filter (fun k => ∃ y ∈ C, ⟪n k, y⟫_ℝ ≠ c k)
  let D := G ∩ avoidsHyperplanes I n c
  have hproper : ∀ k ∈ I, ∃ y ∈ C, ⟪n k, y⟫_ℝ ≠ c k := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  refine ⟨D, inter_subset_left, convex_generic_finite_avoidance C G hC hClosed hG
    I n c hproper, ?_⟩
  intro x hx k hxplane y hy
  by_contra hne
  have hk : k ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ k, y, hy, hne⟩
  exact hx.2 k hk hxplane

/-- The explicit centered equation of an arbitrary placed boundary plane can
be used directly by finite affine-hyperplane avoidance. -/
theorem image_boundaryPlane_eq_uncentered {m J : ℕ} (a : Coefficients m J)
    (b : BoundaryPlaneIndex m) (f : Space m ≃ᵢ Space m) :
    f '' boundaryPlane a b =
      {y | ⟪placedNormal f (boundaryPlaneNormal a b), y⟫_ℝ =
        boundaryPlaneLevel a b +
          ⟪placedNormal f (boundaryPlaneNormal a b), f (boundaryPlaneCenter b)⟫_ℝ} := by
  rw [image_boundaryPlane_eq]
  ext y
  simp only [mem_ofPred_eq, inner_sub_right]
  constructor <;> intro h <;> linarith

/-- Literal key-graph membership already implies actual body membership. -/
theorem keyGraph_subset_body {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) : keyGraph a u ⊆ body a := by
  intro x hx
  exact Or.inr (mem_iUnion.mpr ⟨u, hx.1, hx.2.le⟩)

theorem baseCrease_subset_body {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (s : Side m) : baseCrease a u s ⊆ body a := by
  intro x hx
  exact keyGraph_subset_body a u hx.1.1

theorem sideCrease_subset_body {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (s t : Side m) : sideCrease a u s t ⊆ body a := by
  intro x hx
  exact keyGraph_subset_body a u hx.1.1

/-- A compact convex native subset with a proved dense generic part admits a
dense cross-placement generic subset. The neighbor collection is finite by
packing, and a tile containing a selected point is automatically a neighbor.
The two final conclusions deliberately expose both formulations. -/
theorem placed_crease_crossPlacement_genericity {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (i : ι) (C G : Set (Space m)) (hC : Convex ℝ C) (hCompact : IsCompact C)
    (hG : closure G = C) (hbody : C ⊆ body a) :
    ∃ D : Set (Space m), D ⊆ f i '' G ∧ closure D = f i '' C ∧
      (∀ x ∈ D, ∀ j, (placedBody a (f j) ∩ placedBody a (f i)).Nonempty →
        ∀ b : BoundaryPlaneIndex m, x ∈ f j '' boundaryPlane a b →
          f i '' C ⊆ f j '' boundaryPlane a b) ∧
      (∀ x ∈ D, ∀ j, x ∈ placedBody a (f j) →
        ∀ b : BoundaryPlaneIndex m, x ∈ f j '' boundaryPlane a b →
          f i '' C ⊆ f j '' boundaryPlane a b) := by
  classical
  let N : Set ι := {j | (placedBody a (f j) ∩ placedBody a (f i)).Nonempty}
  let : Fintype N := (finite_placedBody_neighbors a f hdisjoint i).fintype
  let n : N × BoundaryPlaneIndex m → Space m := fun k =>
    placedNormal (f k.1.val) (boundaryPlaneNormal a k.2)
  let c : N × BoundaryPlaneIndex m → ℝ := fun k =>
    boundaryPlaneLevel a k.2 + ⟪n k, f k.1.val (boundaryPlaneCenter k.2)⟫_ℝ
  have hplacedConvex : Convex ℝ (f i '' C) :=
    Convex.affine_image (f i).toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap hC
  have hplacedClosed : IsClosed (f i '' C) := (hCompact.image (f i).continuous).isClosed
  have hplacedDense : closure (f i '' G) = f i '' C := by
    calc
      closure (f i '' G) = (f i).toHomeomorph '' closure G :=
        ((f i).toHomeomorph.image_closure G).symm
      _ = f i '' C := by rw [hG]; rfl
  obtain ⟨D, hDG, hDC, hDplane⟩ := convex_generic_finite_plane_dichotomy
    (f i '' C) (f i '' G) hplacedConvex hplacedClosed hplacedDense n c
  have hneighbor : ∀ x ∈ D, ∀ j,
      (placedBody a (f j) ∩ placedBody a (f i)).Nonempty →
      ∀ b : BoundaryPlaneIndex m, x ∈ f j '' boundaryPlane a b →
        f i '' C ⊆ f j '' boundaryPlane a b := by
    intro x hx j hj b hb
    let k : N × BoundaryPlaneIndex m := (⟨j, hj⟩, b)
    have hbeq : f j '' boundaryPlane a b = {y | ⟪n k, y⟫_ℝ = c k} :=
      image_boundaryPlane_eq_uncentered a b (f j)
    rw [hbeq] at hb ⊢
    exact hDplane x hx k hb
  refine ⟨D, hDG, hDC, hneighbor, ?_⟩
  intro x hx j hj b hb
  have hxC : x ∈ f i '' C := hDC ▸ subset_closure hx
  have hxbody : x ∈ placedBody a (f i) := image_mono hbody hxC
  exact hneighbor x hx j ⟨x, hj, hxbody⟩ b hb

/-- Every literal native base crease has a dense subset of its placed
intrinsically generic points that is generic for all boundary planes of all
neighboring bodies in an arbitrary indexed unrestricted isometric packing.
Any tile containing such a point satisfies the same whole-crease conclusion. -/
theorem genericBaseCrease_crossPlacement {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (i : ι) (u : Site m) (s : Side m) :
    ∃ D : Set (Space m), D ⊆ f i '' genericBaseCrease a u s ∧
      closure D = f i '' baseCrease a u s ∧
      (∀ x ∈ D, ∀ j, (placedBody a (f j) ∩ placedBody a (f i)).Nonempty →
        ∀ b : BoundaryPlaneIndex m, x ∈ f j '' boundaryPlane a b →
          f i '' baseCrease a u s ⊆ f j '' boundaryPlane a b) ∧
      (∀ x ∈ D, ∀ j, x ∈ placedBody a (f j) →
        ∀ b : BoundaryPlaneIndex m, x ∈ f j '' boundaryPlane a b →
          f i '' baseCrease a u s ⊆ f j '' boundaryPlane a b) :=
  placed_crease_crossPlacement_genericity a f hdisjoint i
    (baseCrease a u s) (genericBaseCrease a u s) (baseCrease_convex a u s)
    (baseCrease_isCompact a u s) (genericBaseCrease_closure a u s)
    (baseCrease_subset_body a u s)

/-- The corresponding actual side-side endpoint for every pair of distinct
tangent axes. As for base creases, properness of all deleted planes is proved
inside the construction, rather than assumed from a contact classification. -/
theorem genericSideCrease_crossPlacement {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (i : ι) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    ∃ D : Set (Space m), D ⊆ f i '' genericSideCrease a u s t ∧
      closure D = f i '' sideCrease a u s t ∧
      (∀ x ∈ D, ∀ j, (placedBody a (f j) ∩ placedBody a (f i)).Nonempty →
        ∀ b : BoundaryPlaneIndex m, x ∈ f j '' boundaryPlane a b →
          f i '' sideCrease a u s t ⊆ f j '' boundaryPlane a b) ∧
      (∀ x ∈ D, ∀ j, x ∈ placedBody a (f j) →
        ∀ b : BoundaryPlaneIndex m, x ∈ f j '' boundaryPlane a b →
          f i '' sideCrease a u s t ⊆ f j '' boundaryPlane a b) :=
  placed_crease_crossPlacement_genericity a f hdisjoint i
    (sideCrease a u s t) (genericSideCrease a u s t) (sideCrease_convex a u s t)
    (sideCrease_isCompact a u s t) (genericSideCrease_closure a u s t hst)
    (sideCrease_subset_body a u s t)

#print axioms convex_generic_finite_plane_dichotomy
#print axioms image_boundaryPlane_eq_uncentered
#print axioms keyGraph_subset_body
#print axioms baseCrease_subset_body
#print axioms sideCrease_subset_body
#print axioms placed_crease_crossPlacement_genericity
#print axioms genericBaseCrease_crossPlacement
#print axioms genericSideCrease_crossPlacement
end
end PhysicalRegistration.NativeChair
