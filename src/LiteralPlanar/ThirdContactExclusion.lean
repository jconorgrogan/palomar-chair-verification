module

public import LiteralPlanar.TwoSideOccupation

@[expose] public section


namespace LiteralPlanar
noncomputable section
open Set
variable {X : Type*} [TopologicalSpace X]

/-- A regular-closed tile cannot touch an open region already covered by two
other regular-closed packing tiles. This excludes the extra point contacts
once the actual matched-arc neighborhood has been established. -/
theorem no_third_contact_in_paired_neighborhood (S T V U : Set X) (x : X)
    (hS : S ⊆ closure (interior S)) (hT : T ⊆ closure (interior T))
    (hV : V ⊆ closure (interior V)) (hU : IsOpen U) (hxU : x ∈ U)
    (hcover : U ⊆ S ∪ T)
    (hSV : Disjoint (interior S) (interior V))
    (hTV : Disjoint (interior T) (interior V)) : x ∉ V := by
  have disjoint (W : Set X) (hW : W ⊆ closure (interior W))
      (hd : Disjoint (interior W) (interior V)) : W ⊆ (interior V)ᶜ := by
    have hs : interior W ⊆ (interior V)ᶜ := by
      intro y hy hv
      exact disjoint_left.mp hd hy hv
    exact hW.trans (isOpen_interior.isClosed_compl.closure_subset_iff.mpr hs)
  have hs := disjoint S hS hSV
  have ht := disjoint T hT hTV
  intro hxV
  obtain ⟨y,hyU,hyV⟩ := (mem_closure_iff_nhds.mp (hV hxV)) U (hU.mem_nhds hxU)
  exact (hcover hyU).elim (fun h => hs h hyV) (fun h => ht h hyV)

end
end LiteralPlanar
