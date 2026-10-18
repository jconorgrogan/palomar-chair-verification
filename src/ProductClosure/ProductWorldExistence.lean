module

public import ProductClosure.ProductWorld

@[expose] public section

/-! Products of complete legal generator worlds are actual complete legal
product worlds. No existence certificate is assumed for the product. -/
namespace ProductClosure.World

open Set
noncomputable section
universe u v w z

namespace CompleteTiling
variable {X : Type u} {Y : Type v} {A : Type w} {B : Type z}
  {cellsA : A → Set X} {cellsB : B → Set Y}

/-- The literal Cartesian product of two cell tilings. -/
def prod (WA : CompleteTiling cellsA) (WB : CompleteTiling cellsB) :
    CompleteTiling (productCells cellsA cellsB) where
  tiles := WA.tiles ×ˢ WB.tiles
  cover p := by
    obtain ⟨a, ha, hpa⟩ := WA.cover p.1
    obtain ⟨b, hb, hpb⟩ := WB.cover p.2
    exact ⟨(a, b), ⟨ha, hb⟩, ⟨hpa, hpb⟩⟩
  disjoint p hp q hq hne := Set.disjoint_left.mpr (by
    intro x hxp hxq
    by_cases ha : p.1 = q.1
    · have hb : p.2 ≠ q.2 := fun hb => hne (Prod.ext ha hb)
      exact Set.disjoint_left.mp (WB.disjoint _ hp.2 _ hq.2 hb) hxp.2 hxq.2
    · exact Set.disjoint_left.mp (WA.disjoint _ hp.1 _ hq.1 ha) hxp.1 hxq.1)
  nonempty p hp := by
    obtain ⟨x, hx⟩ := WA.nonempty p.1 hp.1
    obtain ⟨y, hy⟩ := WB.nonempty p.2 hp.2
    exact ⟨(x, y), hx, hy⟩

@[simp] theorem prod_tiles (WA : CompleteTiling cellsA) (WB : CompleteTiling cellsB) :
    (WA.prod WB).tiles = WA.tiles ×ˢ WB.tiles := rfl

@[simp] theorem prod_owner (WA : CompleteTiling cellsA) (WB : CompleteTiling cellsB)
    (p : X × Y) : (WA.prod WB).owner p = (WA.owner p.1, WB.owner p.2) :=
  (WA.prod WB).owner_eq_of_mem ⟨WA.owner_mem p.1, WB.owner_mem p.2⟩
    ⟨WA.mem_owner p.1, WB.mem_owner p.2⟩

/-- Generator-world existence is preserved, for arbitrary factor languages. -/
theorem prod_legal {m n : ℕ} {A : Type u} {B : Type v}
    {cellsA : A → Set (Lattice m)} {cellsB : B → Set (Lattice n)}
    {MA : A → A → Prop} {MB : B → B → Prop}
    (WA : CompleteTiling cellsA) (WB : CompleteTiling cellsB)
    (hA : WA.IsLegal LatticeAdjacent MA) (hB : WB.IsLegal LatticeAdjacent MB) :
    (WA.prod WB).IsLegal ProductAdjacent (ProductLanguage MA MB) := by
  intro p q hadj hne
  simp only [prod_owner] at hne ⊢
  obtain ⟨hpq, hy⟩ | ⟨hx, hpq⟩ := hadj
  · exact Or.inl ⟨hA p.1 q.1 hpq (by
      intro heq
      exact hne (Prod.ext heq (congrArg WB.owner hy))), congrArg WB.owner hy⟩
  · exact Or.inr ⟨congrArg WA.owner hx, hB p.2 q.2 hpq (by
      intro heq
      exact hne (Prod.ext (congrArg WA.owner hx) heq))⟩

/-- The decoded complete factors reconstruct the entire original tile set. -/
theorem factor_product_tiles {m n : ℕ} {A : Type u} {B : Type v}
    {cellsA : A → Set (Lattice m)} {cellsB : B → Set (Lattice n)}
    {MA : A → A → Prop} {MB : B → B → Prop}
    (W : CompleteTiling (productCells cellsA cellsB))
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB) :
    ((W.activeFactor hlegal hsepA hsepB).prod
      (W.passiveFactor hlegal hsepA hsepB)).tiles = W.tiles :=
  (W.tiles_cartesian hlegal hsepA hsepB).symm

/-- Consequently the original and reconstructed cell owner functions agree
pointwise, with equality of complete placed states. -/
theorem factor_product_owner {m n : ℕ} {A : Type u} {B : Type v}
    {cellsA : A → Set (Lattice m)} {cellsB : B → Set (Lattice n)}
    {MA : A → A → Prop} {MB : B → B → Prop}
    (W : CompleteTiling (productCells cellsA cellsB))
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB)
    (p : Lattice m × Lattice n) :
    ((W.activeFactor hlegal hsepA hsepB).prod
      (W.passiveFactor hlegal hsepA hsepB)).owner p = W.owner p := by
  simp only [prod_owner, activeFactor_owner, passiveFactor_owner]
  exact (W.owner_factorizes hlegal hsepA hsepB p.1 p.2).symm

#print axioms prod
#print axioms prod_legal
#print axioms factor_product_tiles

end CompleteTiling
end
end ProductClosure.World
