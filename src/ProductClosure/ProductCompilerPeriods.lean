module

public import ProductClosure.CompilerData
public import ProductClosure.ProductRegisteredContacts
public import ProductClosure.WorldNeighborProfiles
public import ProductClosure.ProductWorldUncast

@[expose] public section

/-! Universal aperiodicity is preserved by the concrete finite-polycube
compiler product. All contact, chart and period projection facts are proved
by the imported physical and complete-world theorems. -/
namespace ProductClosure.CompilerData
open Set
open NativeCompiler ProductGraphSites ProductGraphExact ProductRegisteredContacts
noncomputable section

/-- Every complete legal world of the actual product compiler has zero
translation periods whenever this is true of both concrete input compilers.
This is the repeatable PeriodFree interface; no world factorization,
contact witness, or period projection is an extra premise. -/
theorem prod_periodFree {a b : ℕ} (A : CompilerData a) (B : CompilerData b)
    (hA : A.PeriodFree) (hB : B.PeriodFree) : (A.prod B).PeriodFree := by
  letI : LinearOrder (Site A.cells) := nativeSiteOrder A.dimension
  letI : LinearOrder (Site B.cells) := nativeSiteOrder B.dimension
  letI : LinearOrder (Site (nativeProduct A.cells B.cells)) := nativeSiteOrder (A.prod B).dimension
  intro W hlegal v hperiod
  let hdim := productDim a (b + 1)
  let MA := RegisteredMate A.cells A.generators A.proper
  let MB := RegisteredMate B.cells B.generators B.proper
  have hnative : W.IsLegal World.LatticeAdjacent (fun q r =>
      World.RelativeProductLanguage MA MB (World.castPose hdim.symm (q.relative r))) := by
    intro x y hxy hne
    obtain ⟨hsite, hdisjoint⟩ := neighbor_owners_dense_contact W hxy hne
    have hfull := hlegal x y hxy hne
    change FullProfileMating
      (graphCoefficients (actualProductGraph (SA := A.cells) (SB := B.cells)
        A.generators B.generators A.proper B.proper))
      (PhysicalRegistration.NativeChair.poseIsometry ((W.owner x).relative (W.owner y))) at hfull
    apply registered_product_mate_language (SA := A.cells) (SB := B.cells)
      A.generators B.generators A.proper B.proper
      A.nonempty B.nonempty (World.castPose hdim.symm ((W.owner x).relative (W.owner y)))
    · simpa only [hdim, World.castPose_reverse] using hfull
    · simpa only [hdim, prod, World.castPose_reverse] using hsite
    · simpa only [hdim, prod, World.castPose_reverse] using hdisjoint
  let V := World.CompleteTiling.uncastDimension hdim W
  have hV : V.IsLegal World.LatticeAdjacent (fun q r =>
      World.RelativeProductLanguage MA MB (q.relative r)) := by
    have hh := World.CompleteTiling.uncastDimension_legal hdim W
      (M := fun q => World.RelativeProductLanguage MA MB (World.castPose hdim.symm q)) hnative
    simpa only [World.castPose_symm] using hh
  have hVp := World.CompleteTiling.uncastDimension_hasStatePeriod hdim W v hperiod
  have hv0 : Polycube.castIndex hdim.symm v = 0 := by
    apply V.ambient_period_zero_of_factor_worlds hV
      (registeredMate_separates A.cells A.generators A.proper)
      (registeredMate_separates B.cells B.generators B.proper) ?_ ?_ _ hVp
    · intro WA hWA u hu
      apply hA WA ?_ u hu
      intro x y hxy hne
      exact RegisteredMate.fullProfile (hWA x y hxy hne)
    · intro WB hWB u hu
      apply hB WB ?_ u hu
      intro x y hxy hne
      exact RegisteredMate.fullProfile (hWB x y hxy hne)
  exact (World.castIndex_eq_zero_iff hdim.symm v).mp hv0

#print axioms prod_periodFree
end
end ProductClosure.CompilerData
