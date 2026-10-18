module

public import ProductClosure.ProductGraphCommonExclusions
public import Mathlib.Analysis.Normed.Lp.ProdLp

@[expose] public section

/-! Literal carrier nonoverlap under the actual Euclidean factor lifts. -/
namespace ProductClosure.ProductGraphCarrierDisjoint
noncomputable section
open Set NativeCompiler ProductGraphSites ProductGraphPlacements ProductGraphSiteCoproduct

variable {a b : ℕ}

/-- Physical carrier interiors, prior to any compiled profile restriction. -/
def CarrierDisjoint {m : ℕ} (S : Finset (Polycube.LatticeIndex (m+1)))
    (g : Space m ≃ᵢ Space m) : Prop :=
  Disjoint (interior (Polycube.carrier S)) (interior (g '' Polycube.carrier S))

def productHomeomorph (a b : ℕ) : Space a × Space b ≃ₜ Space (a+(b+1)) :=
  (WithLp.homeomorphProd 2 (Space a) (Space b)).symm.trans
    (splitNative a (b+1)).toHomeomorph.symm

@[simp] theorem productHomeomorph_apply (x : Space a) (y : Space b) :
    productHomeomorph a b (x,y) = appendNative x y :=
  splitNative_symm_pair x y

theorem mem_product_carrier_append
    (SA : Finset (Polycube.LatticeIndex (a+1))) (SB : Finset (Polycube.LatticeIndex (b+1)))
    (x : Space a) (y : Space b) :
    appendNative x y ∈ Polycube.carrier (nativeProduct SA SB) ↔
      x ∈ Polycube.carrier SA ∧ y ∈ Polycube.carrier SB := by
  unfold appendNative nativeProduct
  rw [Polycube.castPoint_mem_carrier, Polycube.mem_carrier_product]
  simp

theorem carrier_product_image
    (SA : Finset (Polycube.LatticeIndex (a+1))) (SB : Finset (Polycube.LatticeIndex (b+1))) :
    productHomeomorph a b '' (Polycube.carrier SA ×ˢ Polycube.carrier SB) =
      Polycube.carrier (nativeProduct SA SB) := by
  ext z
  constructor
  · rintro ⟨⟨x,y⟩, hxy, rfl⟩
    rw [productHomeomorph_apply, mem_product_carrier_append]
    exact hxy
  · intro hz
    obtain ⟨⟨x,y⟩, rfl⟩ := (productHomeomorph a b).surjective z
    refine ⟨(x,y), ?_, rfl⟩
    rwa [productHomeomorph_apply, mem_product_carrier_append] at hz

theorem liftLeft_product_image (g : Space a ≃ᵢ Space a) (A : Set (Space a)) (B : Set (Space b)) :
    liftLeft g '' (productHomeomorph a b '' (A ×ˢ B)) =
      productHomeomorph a b '' ((g '' A) ×ˢ B) := by
  rw [Set.image_image]
  ext z
  constructor
  · rintro ⟨⟨x,y⟩, hxy, rfl⟩
    refine ⟨(g x,y), ⟨⟨x,hxy.1,rfl⟩,hxy.2⟩, ?_⟩
    simp
  · rintro ⟨⟨gx,y⟩, ⟨⟨x,hx,rfl⟩,hy⟩, rfl⟩
    refine ⟨(x,y), ⟨hx,hy⟩, ?_⟩
    simp

theorem liftRight_product_image (g : Space b ≃ᵢ Space b) (A : Set (Space a)) (B : Set (Space b)) :
    commonLiftRight g '' (productHomeomorph a b '' (A ×ˢ B)) =
      productHomeomorph a b '' (A ×ˢ (g '' B)) := by
  rw [Set.image_image]
  ext z
  constructor
  · rintro ⟨⟨x,y⟩, hxy, rfl⟩
    refine ⟨(x,g y), ⟨hxy.1,⟨y,hxy.2,rfl⟩⟩, ?_⟩
    simp
  · rintro ⟨⟨x,gy⟩, ⟨hx,⟨y,hy,rfl⟩⟩, rfl⟩
    refine ⟨(x,y), ⟨hx,hy⟩, ?_⟩
    simp

/-- Every nonempty finite carrier has genuine nonempty interior. -/
theorem carrier_interior_nonempty {d : ℕ} {S : Finset (Polycube.LatticeIndex d)}
    (hS : S.Nonempty) : (interior (Polycube.carrier S)).Nonempty := by
  obtain ⟨z,hz⟩ := hS
  refine ⟨Polycube.latticeCenter z, ?_⟩
  apply interior_mono (show Polycube.latticeCell z ⊆ Polycube.carrier S from
    fun x hx => (Polycube.mem_carrier_iff S x).mpr ⟨z,hz,hx⟩)
  rw [Polycube.interior_latticeCell]
  exact Polycube.latticeCenter_mem_open z

/-- A product with a nonempty passive interior has nonoverlap exactly when
its active factor does. The chart is the actual Euclidean coordinate split. -/
theorem carrierDisjoint_liftLeft_iff
    (SA : Finset (Polycube.LatticeIndex (a+1))) (SB : Finset (Polycube.LatticeIndex (b+1)))
    (hSB : SB.Nonempty) (g : Space a ≃ᵢ Space a) :
    CarrierDisjoint (nativeProduct SA SB) (liftLeft g) ↔ CarrierDisjoint SA g := by
  unfold CarrierDisjoint
  rw [← carrier_product_image SA SB, liftLeft_product_image]
  rw [← (productHomeomorph a b).image_interior, ← (productHomeomorph a b).image_interior,
    Set.disjoint_image_iff (productHomeomorph a b).injective, interior_prod_eq, interior_prod_eq,
    Set.disjoint_prod]
  have hne := carrier_interior_nonempty hSB
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact False.elim (Set.disjoint_left.mp h hne.choose_spec hne.choose_spec)
  · exact Or.inl

theorem carrierDisjoint_liftRight_iff
    (SA : Finset (Polycube.LatticeIndex (a+1))) (SB : Finset (Polycube.LatticeIndex (b+1)))
    (hSA : SA.Nonempty) (g : Space b ≃ᵢ Space b) :
    CarrierDisjoint (nativeProduct SA SB) (commonLiftRight g) ↔ CarrierDisjoint SB g := by
  unfold CarrierDisjoint
  rw [← carrier_product_image SA SB, liftRight_product_image]
  rw [← (productHomeomorph a b).image_interior, ← (productHomeomorph a b).image_interior,
    Set.disjoint_image_iff (productHomeomorph a b).injective, interior_prod_eq, interior_prod_eq,
    Set.disjoint_prod]
  have hne := carrier_interior_nonempty hSA
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim (Set.disjoint_left.mp h hne.choose_spec hne.choose_spec)
    · exact h
  · exact Or.inr

#print axioms carrierDisjoint_liftLeft_iff
#print axioms carrierDisjoint_liftRight_iff
end
end ProductClosure.ProductGraphCarrierDisjoint
