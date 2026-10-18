module

public import ProductClosure.ProductWorldReindex

@[expose] public section

/-! Complete ambient lattice worlds split into complete pair-state worlds
once their common block chart has been derived and normalized. -/
namespace ProductClosure.World

open Set
noncomputable section
variable {m n : ℕ}

/-- Literal concatenation identifies product-grid adjacency with full-grid
adjacency, in both directions. -/
theorem productAdjacent_iff_append (p q : Lattice m × Lattice n) :
    ProductAdjacent p q ↔ LatticeAdjacent (Fin.append p.1 p.2) (Fin.append q.1 q.2) := by
  constructor
  · rintro (⟨⟨i, b, hx⟩, hy⟩ | ⟨hx, ⟨i, b, hy⟩⟩)
    · refine ⟨Fin.castAdd n i, b, ?_⟩
      change Fin.append q.1 q.2 = Polycube.latticeStep (Fin.append p.1 p.2) (Fin.castAdd n i) b
      rw [Polycube.latticeStep_append_left, ← hy]
      exact congrArg (fun z => Fin.append z p.2) hx
    · refine ⟨Fin.natAdd m i, b, ?_⟩
      change Fin.append q.1 q.2 = Polycube.latticeStep (Fin.append p.1 p.2) (Fin.natAdd m i) b
      rw [Polycube.latticeStep_append_right, ← hx]
      exact congrArg (fun z => Fin.append p.1 z) hy
  · rintro ⟨i, b, hq⟩
    revert hq
    refine Fin.addCases ?_ ?_ i
    · intro j hq
      change Fin.append q.1 q.2 = Polycube.latticeStep (Fin.append p.1 p.2) (Fin.castAdd n j) b at hq
      rw [Polycube.latticeStep_append_left] at hq
      have hx := congrArg Polycube.leftIndex hq
      have hy := congrArg Polycube.rightIndex hq
      simp only [Polycube.leftIndex_append, Polycube.rightIndex_append] at hx hy
      exact Or.inl ⟨⟨j, b, hx⟩, hy.symm⟩
    · intro j hq
      change Fin.append q.1 q.2 = Polycube.latticeStep (Fin.append p.1 p.2) (Fin.natAdd m j) b at hq
      rw [Polycube.latticeStep_append_right] at hq
      have hx := congrArg Polycube.leftIndex hq
      have hy := congrArg Polycube.rightIndex hq
      simp only [Polycube.leftIndex_append, Polycube.rightIndex_append] at hx hy
      exact Or.inr ⟨hx.symm, ⟨j, b, hy⟩⟩

namespace CompleteTiling
variable {S : Finset (Lattice m)} {T : Finset (Lattice n)}
variable (W : CompleteTiling (placedCells (Polycube.productCells S T)))
variable (hblock : ∀ q ∈ W.tiles, PreservesBlocks q)

/-- The exact pair of complete factor poses attached to an actual ambient
tile. The proof argument only certifies a previously derived block chart. -/
def splitState (q : {q // q ∈ W.tiles}) : RegisteredPrime.Pose m × RegisteredPrime.Pose n :=
  (leftPose q.val (hblock q.val q.property), rightPose q.val (hblock q.val q.property))

theorem splitState_injective : Function.Injective (W.splitState hblock) := by
  intro q r he
  apply Subtype.ext
  apply splitPose_injective q.val r.val (hblock _ q.property) (hblock _ r.property)
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

/-- Convert a full registered ambient product-carrier world into a literal
pair-state world. Completeness, disjointness, and frame information are all
preserved, rather than supplied as new factorization assumptions. -/
def splitWorld : CompleteTiling (productCells (placedCells S) (placedCells T)) where
  tiles := Set.range (W.splitState hblock)
  cover z := by
    let q : {q // q ∈ W.tiles} := ⟨W.owner (Fin.append z.1 z.2), W.owner_mem _⟩
    refine ⟨W.splitState hblock q, ⟨q, rfl⟩, ?_⟩
    have h := (placedCells_product_iff S T q.val (hblock _ q.property) (Fin.append z.1 z.2)).mp
      (W.mem_owner _)
    simpa only [Polycube.leftIndex_append, Polycube.rightIndex_append, productCells, splitState, Set.mem_prod] using h
  disjoint p hp q hq hne := Set.disjoint_left.mpr (by
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    have hab : a.val ≠ b.val := by
      intro he
      exact hne (congrArg (W.splitState hblock) (Subtype.ext he))
    intro z hz hz'
    have ha : Fin.append z.1 z.2 ∈ placedCells (Polycube.productCells S T) a.val :=
      (placedCells_product_iff S T a.val (hblock _ a.property) _).mpr (by simpa only [Polycube.leftIndex_append, Polycube.rightIndex_append, productCells, splitState, Set.mem_prod] using hz)
    have hb : Fin.append z.1 z.2 ∈ placedCells (Polycube.productCells S T) b.val :=
      (placedCells_product_iff S T b.val (hblock _ b.property) _).mpr (by simpa only [Polycube.leftIndex_append, Polycube.rightIndex_append, productCells, splitState, Set.mem_prod] using hz')
    exact Set.disjoint_left.mp (W.disjoint _ a.property _ b.property hab) ha hb)
  nonempty p hp := by
    obtain ⟨q, rfl⟩ := hp
    obtain ⟨z, hz⟩ := W.nonempty q.val q.property
    exact ⟨(Polycube.leftIndex z, Polycube.rightIndex z),
      (placedCells_product_iff S T q.val (hblock _ q.property) z).mp hz⟩

@[simp] theorem splitWorld_tiles :
    (W.splitWorld hblock).tiles = Set.range (W.splitState hblock) := rfl

/-- Every split owner is exactly the full ambient owner's two restricted
poses, so no local or global labeling information is lost. -/
theorem splitWorld_owner (z : Lattice m × Lattice n) :
    (W.splitWorld hblock).owner z = W.splitState hblock
      ⟨W.owner (Fin.append z.1 z.2), W.owner_mem _⟩ := by
  apply (W.splitWorld hblock).owner_eq_of_mem
  · exact ⟨⟨W.owner (Fin.append z.1 z.2), W.owner_mem _⟩, rfl⟩
  · have h := (placedCells_product_iff S T (W.owner (Fin.append z.1 z.2))
      (hblock _ (W.owner_mem _)) _).mp (W.mem_owner _)
    simpa only [Polycube.leftIndex_append, Polycube.rightIndex_append, productCells, splitState, Set.mem_prod] using h

/-- A local physical/carrier contact-language theorem, expressed on occupied
neighboring full-grid cells, transfers to the split owner world. -/
theorem splitWorld_legal
    {MA : RegisteredPrime.Pose m → RegisteredPrime.Pose m → Prop}
    {MB : RegisteredPrime.Pose n → RegisteredPrime.Pose n → Prop}
    (hcontact : ∀ (q r : {q // q ∈ W.tiles}), q.val ≠ r.val →
      (∃ x y, x ∈ placedCells (Polycube.productCells S T) q.val ∧
        y ∈ placedCells (Polycube.productCells S T) r.val ∧ LatticeAdjacent x y) →
      ProductLanguage MA MB (W.splitState hblock q) (W.splitState hblock r)) :
    (W.splitWorld hblock).IsLegal ProductAdjacent (ProductLanguage MA MB) := by
  intro z w hadj hne
  rw [splitWorld_owner, splitWorld_owner] at hne ⊢
  apply hcontact
  · intro he
    exact hne (congrArg (W.splitState hblock) (Subtype.ext he))
  · exact ⟨Fin.append z.1 z.2, Fin.append w.1 w.2, W.mem_owner _, W.mem_owner _,
      (productAdjacent_iff_append z w).mp hadj⟩

/-- After the common chart is proved, exact local split contact closure
produces complete legal factor worlds and an exact Cartesian state set. -/
theorem splitWorld_cartesian
    {MA : RegisteredPrime.Pose m → RegisteredPrime.Pose m → Prop}
    {MB : RegisteredPrime.Pose n → RegisteredPrime.Pose n → Prop}
    (hcontact : ∀ (q r : {q // q ∈ W.tiles}), q.val ≠ r.val →
      (∃ x y, x ∈ placedCells (Polycube.productCells S T) q.val ∧
        y ∈ placedCells (Polycube.productCells S T) r.val ∧ LatticeAdjacent x y) →
      ProductLanguage MA MB (W.splitState hblock q) (W.splitState hblock r))
    (hsepA : Separates (placedCells S) MA) (hsepB : Separates (placedCells T) MB) :
    ∃ (WA : CompleteTiling (placedCells S)) (WB : CompleteTiling (placedCells T)),
      WA.IsLegal LatticeAdjacent MA ∧ WB.IsLegal LatticeAdjacent MB ∧
      Set.range (W.splitState hblock) = WA.tiles ×ˢ WB.tiles ∧
      ∀ z, (W.splitWorld hblock).owner z = (WA.owner z.1, WB.owner z.2) := by
  let C := W.splitWorld hblock
  have hl := W.splitWorld_legal hblock hcontact
  refine ⟨C.activeFactor hl hsepA hsepB, C.passiveFactor hl hsepA hsepB,
    C.activeFactor_legal hl hsepA hsepB, C.passiveFactor_legal hl hsepA hsepB,
    C.tiles_cartesian hl hsepA hsepB, ?_⟩
  intro z
  simp only [activeFactor_owner, passiveFactor_owner]
  exact C.owner_factorizes hl hsepA hsepB z.1 z.2

#print axioms splitState_injective
#print axioms splitWorld
#print axioms splitWorld_legal
#print axioms splitWorld_cartesian

end CompleteTiling
end
end ProductClosure.World
