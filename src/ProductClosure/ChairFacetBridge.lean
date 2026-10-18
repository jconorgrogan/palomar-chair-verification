module

public import ProductClosure.ChairCarrierBridge
public import PrimeFacetClosure.NativeContactFacet

@[expose] public section

/-! Exact chair facet/site reindexing for the arbitrary-polycube compiler. -/
namespace ProductClosure.ChairBridge
open Set
noncomputable section

private theorem latticeStep_direction_injective {d : ℕ}
    (z : Polycube.LatticeIndex d) (i j : Fin d) (b c : Bool)
    (h : Polycube.latticeStep z i b = Polycube.latticeStep z j c) : i = j ∧ b = c := by
  have hij : i = j := by
    by_contra hh
    have hi := congrFun h i
    cases b <;> simp [Polycube.latticeStep, hh] at hi
  subst j
  refine ⟨rfl, ?_⟩
  have hi := congrFun h i
  cases b <;> cases c <;> simp_all [Polycube.latticeStep]

theorem facetMap_injective {m : ℕ} : Function.Injective (@facetMap m) := by
  intro f g h
  have ha := congrArg Polycube.Facet.axis h
  have hc := congrArg Polycube.facetCenter h
  simp only [facetMap_axis, facetMap_center] at ha hc
  apply PhysicalRegistration.NativeChair.facet_eq_of_coordinate_data f g ha
  · have hi := congrArg (fun x : Polycube.Space (m+1) => x (PhysicalRegistration.NativeChair.normalIndex f)) hc
    rw [PhysicalRegistration.NativeChair.facetCenter_normal, ha,
      PhysicalRegistration.NativeChair.facetCenter_normal] at hi
    exact Int.cast_injective hi
  · intro k hk
    have hi := congrArg (fun x : Polycube.Space (m+1) => x k) hc
    rw [PhysicalRegistration.NativeChair.facetCenter_tangent f k hk,
      PhysicalRegistration.NativeChair.facetCenter_tangent g k (ha ▸ hk)] at hi
    exact_mod_cast (show (PhysicalRegistration.NativeChair.facetCellCoordinate f k : ℝ) =
      (PhysicalRegistration.NativeChair.facetCellCoordinate g k : ℝ) by linarith)

theorem facetMap_surjective {m : ℕ} : Function.Surjective (@facetMap m) := by
  intro F
  obtain ⟨c,hc⟩ := (cellMap_bijective m).2 F.cell
  have hcv : PhysicalRegistration.NativeChair.cellIndex c = F.cell.val := congrArg Subtype.val hc
  let z := Polycube.facetOutsideIndex F
  have hadj : RegisteredPrime.Adjacent (PhysicalRegistration.NativeChair.cellIndex c) z := by
    rw [hcv]
    refine ⟨F.axis, ?_, ?_⟩
    · cases hp : F.positive <;> simp [z, Polycube.facetOutsideIndex, Polycube.latticeStep, hp]
    · intro k hk
      simp [z, Polycube.facetOutsideIndex, Polycube.latticeStep, hk]
  have hout : ¬ ∃ b : PhysicalRegistration.NativeChair.Cell m,
      PhysicalRegistration.NativeChair.cellIndex b = z := by
    rintro ⟨b,hb⟩
    apply F.outside
    change z ∈ cells m
    rw [← hb]
    exact (cellMap b).property
  obtain ⟨f,hf,hfo⟩ := PhysicalRegistration.NativeChair.native_cell_exposed_neighbor c z hadj hout
  refine ⟨f, ?_⟩
  have hfc : (facetMap f).cell = F.cell := by simp only [facetMap_inside, hf, hc]
  have hs : Polycube.latticeStep F.cell.val (facetMap f).axis (facetMap f).positive =
      Polycube.latticeStep F.cell.val F.axis F.positive := by
    conv_lhs => rw [← hfc]
    exact hfo
  obtain ⟨ha,hp⟩ := latticeStep_direction_injective _ _ _ _ _ hs
  exact Polycube.Facet.ext hfc ha hp

def facetEquiv (m : ℕ) : PhysicalRegistration.NativeChair.Facet m ≃ Polycube.Facet (cells m) :=
  Equiv.ofBijective facetMap ⟨facetMap_injective, facetMap_surjective⟩

def siteEquiv (m : ℕ) : PhysicalRegistration.NativeChair.Site m ≃ NativeCompiler.Site (cells m) :=
  Equiv.prodCongr (facetEquiv m) (Equiv.refl _)

@[simp] theorem siteEquiv_axis {m : ℕ} (u : PhysicalRegistration.NativeChair.Site m) (j : Fin m) :
    NativeCompiler.siteAxis (siteEquiv m u) j = PhysicalRegistration.NativeChair.siteAxis u j := rfl

@[simp] theorem siteEquiv_center {m : ℕ} (u : PhysicalRegistration.NativeChair.Site m) :
    NativeCompiler.siteCenter (siteEquiv m u) = PhysicalRegistration.NativeChair.siteCenter u := by
  change Polycube.facetCenter (facetMap u.1) + _ = _
  rw [facetMap_center]
  rfl

@[simp] theorem siteEquiv_outward {m : ℕ} (u : PhysicalRegistration.NativeChair.Site m) :
    NativeCompiler.outward (siteEquiv m u).1 = PhysicalRegistration.NativeChair.outward u.1 :=
  facetMap_outward u.1

end
end ProductClosure.ChairBridge
