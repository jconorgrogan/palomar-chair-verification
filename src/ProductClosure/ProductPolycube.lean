module

public import ProductClosure.Polycube
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! Literal products of finite integer polycubes, with exact exposed facets. -/
namespace ProductClosure.Polycube
open Set
noncomputable section

variable {m n : ℕ}

def leftIndex (z : LatticeIndex (m + n)) : LatticeIndex m := fun i => z (Fin.castAdd n i)
def rightIndex (z : LatticeIndex (m + n)) : LatticeIndex n := fun i => z (Fin.natAdd m i)

@[simp] theorem leftIndex_append (z : LatticeIndex m) (w : LatticeIndex n) :
    leftIndex (Fin.append z w) = z := by funext i; simp [leftIndex]
@[simp] theorem rightIndex_append (z : LatticeIndex m) (w : LatticeIndex n) :
    rightIndex (Fin.append z w) = w := by funext i; simp [rightIndex]
@[simp] theorem append_leftIndex_rightIndex (z : LatticeIndex (m + n)) :
    Fin.append (leftIndex z) (rightIndex z) = z := Fin.append_castAdd_natAdd

theorem append_indices_injective : Function.Injective
    (fun p : LatticeIndex m × LatticeIndex n => Fin.append p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · simpa using congrArg leftIndex h
  · simpa using congrArg rightIndex h

def productCells (S : Finset (LatticeIndex m)) (T : Finset (LatticeIndex n)) :
    Finset (LatticeIndex (m + n)) :=
  (S ×ˢ T).image (fun p => Fin.append p.1 p.2)

@[simp] theorem mem_productCells (S : Finset (LatticeIndex m)) (T : Finset (LatticeIndex n))
    (z : LatticeIndex (m + n)) : z ∈ productCells S T ↔ leftIndex z ∈ S ∧ rightIndex z ∈ T := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp h
    simpa using Finset.mem_product.mp hab
  · intro h
    exact Finset.mem_image.mpr ⟨(leftIndex z, rightIndex z), Finset.mem_product.mpr h,
      append_leftIndex_rightIndex z⟩

@[simp] theorem append_mem_productCells (S : Finset (LatticeIndex m)) (T : Finset (LatticeIndex n))
    (z : LatticeIndex m) (w : LatticeIndex n) :
    Fin.append z w ∈ productCells S T ↔ z ∈ S ∧ w ∈ T := by simp

theorem productCells_nonempty {S : Finset (LatticeIndex m)} {T : Finset (LatticeIndex n)}
    (hS : S.Nonempty) (hT : T.Nonempty) : (productCells S T).Nonempty :=
  (hS.product hT).image _

theorem productCells_card (S : Finset (LatticeIndex m)) (T : Finset (LatticeIndex n)) :
    (productCells S T).card = S.card * T.card := by
  rw [productCells, Finset.card_image_of_injective _ append_indices_injective, Finset.card_product]

/-- Occupied product cells retain both original occupied cell indices. -/
def productCellEquiv (S : Finset (LatticeIndex m)) (T : Finset (LatticeIndex n)) :
    Cell (productCells S T) ≃ Cell S × Cell T where
  toFun c := (⟨leftIndex c.val, ((mem_productCells S T c.val).mp c.property).1⟩,
    ⟨rightIndex c.val, ((mem_productCells S T c.val).mp c.property).2⟩)
  invFun p := ⟨Fin.append p.1.val p.2.val, (append_mem_productCells S T _ _).mpr
    ⟨p.1.property, p.2.property⟩⟩
  left_inv c := Subtype.ext (append_leftIndex_rightIndex c.val)
  right_inv p := by cases p; simp

@[simp] theorem latticeStep_append_left (z : LatticeIndex m) (w : LatticeIndex n)
    (i : Fin m) (b : Bool) :
    latticeStep (Fin.append z w) (Fin.castAdd n i) b = Fin.append (latticeStep z i b) w := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro j
    simp [latticeStep]
  · intro j
    have hne : Fin.natAdd m j ≠ Fin.castAdd n i := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    simp [latticeStep, hne]

@[simp] theorem latticeStep_append_right (z : LatticeIndex m) (w : LatticeIndex n)
    (i : Fin n) (b : Bool) :
    latticeStep (Fin.append z w) (Fin.natAdd m i) b = Fin.append z (latticeStep w i b) := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro j
    have hne : Fin.castAdd n j ≠ Fin.natAdd m i := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    simp [latticeStep, hne]
  · intro j
    simp [latticeStep]

variable {S : Finset (LatticeIndex m)} {T : Finset (LatticeIndex n)}

/-- An active left facet paired with a passive occupied right cell. -/
def productFacetLeft (f : Facet S) (c : Cell T) : Facet (productCells S T) where
  cell := (productCellEquiv S T).symm (f.cell, c)
  axis := Fin.castAdd n f.axis
  positive := f.positive
  outside := by
    change latticeStep (Fin.append f.cell.val c.val) (Fin.castAdd n f.axis) f.positive ∉ _
    rw [latticeStep_append_left, append_mem_productCells]
    exact fun h => f.outside h.1

/-- An active right facet paired with a passive occupied left cell. -/
def productFacetRight (c : Cell S) (f : Facet T) : Facet (productCells S T) where
  cell := (productCellEquiv S T).symm (c, f.cell)
  axis := Fin.natAdd m f.axis
  positive := f.positive
  outside := by
    change latticeStep (Fin.append c.val f.cell.val) (Fin.natAdd m f.axis) f.positive ∉ _
    rw [latticeStep_append_right, append_mem_productCells]
    exact fun h => f.outside h.2

@[ext] theorem Facet.ext {d : ℕ} {U : Finset (LatticeIndex d)} {f g : Facet U}
    (hc : f.cell = g.cell) (ha : f.axis = g.axis) (hp : f.positive = g.positive) : f = g := by
  cases f; cases g
  simp_all

theorem productFacetLeft_injective : Function.Injective
    (fun p : Facet S × Cell T => productFacetLeft p.1 p.2) := by
  intro p q h
  have hc := congrArg (fun f => f.cell.val) h
  have ha := congrArg Facet.axis h
  have hp := congrArg Facet.positive h
  apply Prod.ext
  · apply Facet.ext
    · apply Subtype.ext
      simpa [productFacetLeft, productCellEquiv] using congrArg leftIndex hc
    · simpa [productFacetLeft] using ha
    · exact hp
  · apply Subtype.ext
    simpa [productFacetLeft, productCellEquiv] using congrArg rightIndex hc

theorem productFacetRight_injective : Function.Injective
    (fun p : Cell S × Facet T => productFacetRight p.1 p.2) := by
  intro p q h
  have hc := congrArg (fun f => f.cell.val) h
  have ha := congrArg Facet.axis h
  have hp := congrArg Facet.positive h
  apply Prod.ext
  · apply Subtype.ext
    simpa [productFacetRight, productCellEquiv] using congrArg leftIndex hc
  · apply Facet.ext
    · apply Subtype.ext
      simpa [productFacetRight, productCellEquiv] using congrArg rightIndex hc
    · simpa [productFacetRight] using ha
    · exact hp

def productFacetMap : (Facet S × Cell T) ⊕ (Cell S × Facet T) → Facet (productCells S T) :=
  Sum.elim (fun p => productFacetLeft p.1 p.2) (fun p => productFacetRight p.1 p.2)

theorem productFacetMap_injective : Function.Injective (@productFacetMap m n S T) := by
  intro p q h
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (productFacetLeft_injective h)
    | inr q =>
      have ha := congrArg (fun f => f.axis.val) h
      simp only [productFacetMap, Sum.elim_inl, Sum.elim_inr, productFacetLeft,
        productFacetRight, Fin.val_castAdd, Fin.val_natAdd] at ha
      have hi := p.1.axis.isLt
      omega
  | inr p =>
    cases q with
    | inl q =>
      have ha := congrArg (fun f => f.axis.val) h
      simp only [productFacetMap, Sum.elim_inl, Sum.elim_inr, productFacetLeft,
        productFacetRight, Fin.val_castAdd, Fin.val_natAdd] at ha
      have hi := q.1.axis.isLt
      omega
    | inr q => exact congrArg Sum.inr (productFacetRight_injective h)

theorem productFacetMap_surjective : Function.Surjective (@productFacetMap m n S T) := by
  intro f
  have hc := (mem_productCells S T f.cell.val).mp f.cell.property
  have haxis : (∃ i : Fin m, f.axis = Fin.castAdd n i) ∨
      (∃ i : Fin n, f.axis = Fin.natAdd m i) := by
    obtain ⟨i, hi⟩ := finSumFinEquiv.surjective f.axis
    cases i with
    | inl i => exact Or.inl ⟨i, hi.symm⟩
    | inr i => exact Or.inr ⟨i, hi.symm⟩
  rcases haxis with ⟨i, ha⟩ | ⟨i, ha⟩
  · have hout : latticeStep (leftIndex f.cell.val) i f.positive ∉ S := by
      intro h
      apply f.outside
      rw [← append_leftIndex_rightIndex f.cell.val]
      rw [ha, latticeStep_append_left, append_mem_productCells]
      exact ⟨h, hc.2⟩
    let fa : Facet S := ⟨⟨leftIndex f.cell.val, hc.1⟩, i, f.positive, hout⟩
    let cb : Cell T := ⟨rightIndex f.cell.val, hc.2⟩
    refine ⟨Sum.inl (fa, cb), ?_⟩
    apply Facet.ext
    · apply Subtype.ext
      exact append_leftIndex_rightIndex f.cell.val
    · exact ha.symm
    · rfl
  · have hout : latticeStep (rightIndex f.cell.val) i f.positive ∉ T := by
      intro h
      apply f.outside
      rw [← append_leftIndex_rightIndex f.cell.val]
      rw [ha, latticeStep_append_right, append_mem_productCells]
      exact ⟨hc.1, h⟩
    let ca : Cell S := ⟨leftIndex f.cell.val, hc.1⟩
    let fb : Facet T := ⟨⟨rightIndex f.cell.val, hc.2⟩, i, f.positive, hout⟩
    refine ⟨Sum.inr (ca, fb), ?_⟩
    apply Facet.ext
    · apply Subtype.ext
      exact append_leftIndex_rightIndex f.cell.val
    · exact ha.symm
    · rfl

/-- The exact exposed-product-facet decomposition. The passive factor is a
literal occupied cell, not merely an arbitrary auxiliary label. -/
def productFacetEquiv (S : Finset (LatticeIndex m)) (T : Finset (LatticeIndex n)) :
    (Facet S × Cell T) ⊕ (Cell S × Facet T) ≃ Facet (productCells S T) :=
  Equiv.ofBijective productFacetMap ⟨productFacetMap_injective, productFacetMap_surjective⟩

@[simp] theorem leftAxis_ne_rightAxis (i : Fin m) (j : Fin n) :
    Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

@[simp] theorem rightAxis_ne_leftAxis (j : Fin n) (i : Fin m) :
    Fin.natAdd m j ≠ Fin.castAdd n i := Ne.symm (leftAxis_ne_rightAxis i j)

def appendPoint (x : Space m) (y : Space n) : Space (m + n) :=
  WithLp.toLp 2 (Fin.append (fun i => x i) (fun i => y i))
def leftPoint (x : Space (m + n)) : Space m :=
  WithLp.toLp 2 (fun i => x (Fin.castAdd n i))
def rightPoint (x : Space (m + n)) : Space n :=
  WithLp.toLp 2 (fun i => x (Fin.natAdd m i))

@[simp] theorem leftPoint_appendPoint (x : Space m) (y : Space n) :
    leftPoint (appendPoint x y) = x := by ext i; simp [leftPoint, appendPoint]
@[simp] theorem rightPoint_appendPoint (x : Space m) (y : Space n) :
    rightPoint (appendPoint x y) = y := by ext i; simp [rightPoint, appendPoint]
@[simp] theorem appendPoint_leftPoint_rightPoint (x : Space (m + n)) :
    appendPoint (leftPoint x) (rightPoint x) = x := by
  ext i
  exact congrFun (Fin.append_castAdd_natAdd (f := fun j => x j)) i

@[simp] theorem latticeCenter_append (z : LatticeIndex m) (w : LatticeIndex n) :
    latticeCenter (Fin.append z w) = appendPoint (latticeCenter z) (latticeCenter w) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [latticeCenter, appendPoint]

theorem mem_latticeCell_append (z : LatticeIndex m) (w : LatticeIndex n) (x : Space (m + n)) :
    x ∈ latticeCell (Fin.append z w) ↔
      leftPoint x ∈ latticeCell z ∧ rightPoint x ∈ latticeCell w := by
  constructor
  · intro h
    constructor
    · intro i; simpa [leftPoint] using h (Fin.castAdd n i)
    · intro i; simpa [rightPoint] using h (Fin.natAdd m i)
  · intro h k
    refine Fin.addCases ?_ ?_ k
    · intro i; simpa [leftPoint] using h.1 i
    · intro i; simpa [rightPoint] using h.2 i

/-- The literal finite closed-cell union is exactly the Cartesian carrier
product in the explicit coordinate concatenation chart. -/
theorem mem_carrier_product (x : Space (m + n)) :
    x ∈ carrier (productCells S T) ↔ leftPoint x ∈ carrier S ∧ rightPoint x ∈ carrier T := by
  constructor
  · intro h
    obtain ⟨z, hz, hx⟩ := (mem_carrier_iff _ _).mp h
    have hst := (mem_productCells S T z).mp hz
    have hcell : leftPoint x ∈ latticeCell (leftIndex z) ∧
        rightPoint x ∈ latticeCell (rightIndex z) := by
      apply (mem_latticeCell_append _ _ x).mp
      simpa using hx
    exact ⟨(mem_carrier_iff _ _).mpr ⟨_, hst.1, hcell.1⟩,
      (mem_carrier_iff _ _).mpr ⟨_, hst.2, hcell.2⟩⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨z, hz, hx⟩ := (mem_carrier_iff _ _).mp hx
    obtain ⟨w, hw, hy⟩ := (mem_carrier_iff _ _).mp hy
    exact (mem_carrier_iff _ _).mpr ⟨Fin.append z w,
      (append_mem_productCells S T z w).mpr ⟨hz, hw⟩,
      (mem_latticeCell_append z w x).mpr ⟨hx, hy⟩⟩

@[simp] theorem productFacetLeft_plane (f : Facet S) (c : Cell T) :
    facetPlane (productFacetLeft f c) = facetPlane f := by
  simp only [facetPlane, productFacetLeft, productCellEquiv, Equiv.coe_fn_symm_mk, Fin.append_left]
  rfl
@[simp] theorem productFacetRight_plane (c : Cell S) (f : Facet T) :
    facetPlane (productFacetRight c f) = facetPlane f := by
  simp only [facetPlane, productFacetRight, productCellEquiv, Equiv.coe_fn_symm_mk, Fin.append_right]
  rfl

@[simp] theorem productFacetLeft_outward (f : Facet S) (c : Cell T) :
    outward (productFacetLeft f c) = appendPoint (outward f) 0 := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [outward_apply, productFacetLeft, appendPoint]
@[simp] theorem productFacetRight_outward (c : Cell S) (f : Facet T) :
    outward (productFacetRight c f) = appendPoint 0 (outward f) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [outward_apply, productFacetRight, appendPoint]

@[simp] theorem productFacetLeft_center (f : Facet S) (c : Cell T) :
    facetCenter (productFacetLeft f c) = appendPoint (facetCenter f) (latticeCenter c.val) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [facetCenter, latticeCenter, outward_apply, productFacetLeft, productCellEquiv, appendPoint]
@[simp] theorem productFacetRight_center (c : Cell S) (f : Facet T) :
    facetCenter (productFacetRight c f) = appendPoint (latticeCenter c.val) (facetCenter f) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [facetCenter, latticeCenter, outward_apply, productFacetRight, productCellEquiv, appendPoint]

/-- The geometric facet decomposition gives the exact finite facet count. -/
theorem productFacet_card (S : Finset (LatticeIndex m)) (T : Finset (LatticeIndex n)) :
    Fintype.card (Facet (productCells S T)) =
      Fintype.card (Facet S) * T.card + S.card * Fintype.card (Facet T) := by
  rw [← Fintype.card_congr (productFacetEquiv S T)]
  simp

end
end ProductClosure.Polycube
