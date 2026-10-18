module

public import ProductClosure.ProductPolycube

@[expose] public section

/-! Canonical equal-dimension reindexing, including literal cells and facets. -/
namespace ProductClosure.Polycube
noncomputable section

variable {d e : ℕ}

def castIndex (h : d = e) (z : LatticeIndex d) : LatticeIndex e :=
  fun k => z (Fin.cast h.symm k)

def castPoint (h : d = e) (x : Space d) : Space e :=
  WithLp.toLp 2 (fun k => x (Fin.cast h.symm k))

def castCells (h : d = e) (S : Finset (LatticeIndex d)) : Finset (LatticeIndex e) := h ▸ S

def castCellEquiv (h : d = e) (S : Finset (LatticeIndex d)) : Cell S ≃ Cell (castCells h S) := by
  subst e
  exact Equiv.refl _

def castFacetEquiv (h : d = e) (S : Finset (LatticeIndex d)) : Facet S ≃ Facet (castCells h S) := by
  subst e
  exact Equiv.refl _

@[simp] theorem castIndex_refl (z : LatticeIndex d) : castIndex rfl z = z := rfl
@[simp] theorem castPoint_refl (x : Space d) : castPoint rfl x = x := rfl
@[simp] theorem castCells_refl (S : Finset (LatticeIndex d)) : castCells rfl S = S := rfl

@[simp] theorem castIndex_apply (h : d = e) (z : LatticeIndex d) (k : Fin d) :
    castIndex h z (Fin.cast h k) = z k := by subst e; rfl
@[simp] theorem castPoint_apply (h : d = e) (x : Space d) (k : Fin d) :
    castPoint h x (Fin.cast h k) = x k := by subst e; rfl
@[simp] theorem castIndex_mem_castCells (h : d = e) (S : Finset (LatticeIndex d)) (z : LatticeIndex d) :
    castIndex h z ∈ castCells h S ↔ z ∈ S := by subst e; rfl
@[simp] theorem castCellEquiv_val (h : d = e) (S : Finset (LatticeIndex d)) (c : Cell S) :
    (castCellEquiv h S c).val = castIndex h c.val := by subst e; rfl
@[simp] theorem castFacetEquiv_cell (h : d = e) (S : Finset (LatticeIndex d)) (f : Facet S) :
    (castFacetEquiv h S f).cell = castCellEquiv h S f.cell := by subst e; rfl
@[simp] theorem castFacetEquiv_axis (h : d = e) (S : Finset (LatticeIndex d)) (f : Facet S) :
    (castFacetEquiv h S f).axis = Fin.cast h f.axis := by subst e; rfl
@[simp] theorem castFacetEquiv_positive (h : d = e) (S : Finset (LatticeIndex d)) (f : Facet S) :
    (castFacetEquiv h S f).positive = f.positive := by subst e; rfl
@[simp] theorem castFacetEquiv_plane (h : d = e) (S : Finset (LatticeIndex d)) (f : Facet S) :
    facetPlane (castFacetEquiv h S f) = facetPlane f := by subst e; rfl
@[simp] theorem castFacetEquiv_center (h : d = e) (S : Finset (LatticeIndex d)) (f : Facet S) :
    facetCenter (castFacetEquiv h S f) = castPoint h (facetCenter f) := by subst e; rfl
@[simp] theorem castFacetEquiv_outward (h : d = e) (S : Finset (LatticeIndex d)) (f : Facet S) :
    outward (castFacetEquiv h S f) = castPoint h (outward f) := by subst e; rfl
@[simp] theorem castFacetEquiv_outsideIndex (h : d = e) (S : Finset (LatticeIndex d)) (f : Facet S) :
    facetOutsideIndex (castFacetEquiv h S f) = castIndex h (facetOutsideIndex f) := by subst e; rfl
@[simp] theorem castPoint_latticeCenter (h : d = e) (z : LatticeIndex d) :
    castPoint h (latticeCenter z) = latticeCenter (castIndex h z) := by subst e; rfl
@[simp] theorem castPoint_mem_latticeCell (h : d = e) (z : LatticeIndex d) (x : Space d) :
    castPoint h x ∈ latticeCell (castIndex h z) ↔ x ∈ latticeCell z := by subst e; rfl
@[simp] theorem castPoint_mem_carrier (h : d = e) (S : Finset (LatticeIndex d)) (x : Space d) :
    castPoint h x ∈ carrier (castCells h S) ↔ x ∈ carrier S := by subst e; rfl

end
end ProductClosure.Polycube
