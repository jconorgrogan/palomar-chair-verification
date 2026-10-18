module

public import Mathlib.Topology.IsLocalHomeomorph

@[expose] public section


/-! A carrier-subspace homeomorphism gives an ambient local homeomorphism
where both source and target carrier interior conditions hold. No closedness,
compactness, or global carrier coverage is assumed. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Restrict to points interior to both carriers. The given global continuous
map becomes an open embedding there. -/
theorem isOpenEmbedding_carrier_interiors
    (F : X → Y) (hF : Continuous F) (S : Set X) (T : Set Y)
    (h : S ≃ₜ T) (hagree : ∀ y : S, F y = (h y : Y)) :
    IsOpenEmbedding ((interior S ∩ F ⁻¹' interior T).domRestrict F) := by
  let U := interior S ∩ F ⁻¹' interior T
  have hU : IsOpen U := isOpen_interior.inter (isOpen_interior.preimage hF)
  have hUS : U ⊆ S := fun _ hx => interior_subset hx.1
  let g : U → T := fun z => h (Set.inclusion hUS z)
  have hg : IsOpenMap g := h.isOpenMap.comp (hU.isOpenMap_inclusion hUS)
  have hgf (z : U) : (g z : Y) = F z := (hagree (Set.inclusion hUS z)).symm
  have hinj : Function.Injective (U.domRestrict F) := by
    intro a b hab
    have hh : g a = g b := Subtype.ext (by rw [hgf,hgf]; exact hab)
    have hi := h.injective hh
    exact Subtype.ext (congrArg (fun z : S => (z : X)) hi)
  have hopen : IsOpenMap (U.domRestrict F) := by
    intro V hV
    obtain ⟨W,hW,hWV⟩ := (hg V hV).image_val
    have himage : (U.domRestrict F) '' V = (Subtype.val : T → Y) '' (g '' V) := by
      rw [Set.image_image]
      apply Set.image_congr
      intro z hz
      exact (hgf z).symm
    have hsub : (U.domRestrict F) '' V ⊆ interior T := by
      rintro y ⟨z,hz,rfl⟩
      exact z.property.2
    have heq : (U.domRestrict F) '' V = W ∩ interior T := by
      rw [himage,hWV] at hsub ⊢
      ext y
      exact ⟨fun hy => ⟨hy.1,hsub hy⟩,
        fun hy => ⟨hy.1,interior_subset hy.2⟩⟩
    rw [heq]
    exact hW.inter isOpen_interior
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hF.comp continuous_subtype_val) hinj hopen

/-- Every point interior to both carriers has an ambient local homeomorphism
whose forward map is exactly F, including away from its local source. -/
theorem isLocalHomeomorphOn_carrier_interiors
    (F : X → Y) (hF : Continuous F) (S : Set X) (T : Set Y)
    (h : S ≃ₜ T) (hagree : ∀ y : S, F y = (h y : Y)) :
    IsLocalHomeomorphOn F (interior S ∩ F ⁻¹' interior T) := by
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
  intro x hx
  refine ⟨interior S ∩ F ⁻¹' interior T,
    (isOpen_interior.inter (isOpen_interior.preimage hF)).mem_nhds hx,?_⟩
  exact isOpenEmbedding_carrier_interiors F hF S T h hagree

/-- All-carrier agreement specialization for a finite-star homeomorphism.
Both interior hypotheses are explicit. -/
theorem exists_openPartialHomeomorph_of_carrier_homeomorph
    (F : X → Y) (hF : Continuous F) (S : Set X) (T : Set Y)
    (h : S ≃ₜ T) (hagree : ∀ y : S, F y = (h y : Y))
    (x : X) (hx : x ∈ interior S) (hFx : F x ∈ interior T) :
    ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ F = e :=
  isLocalHomeomorphOn_carrier_interiors F hF S T h hagree x ⟨hx,hFx⟩

/-- An ambient local homeomorphism is obtained from one such carrier chart
at every point. The carriers may depend on the point. -/
theorem isLocalHomeomorph_of_carrier_charts
    (F : X → Y) (hF : Continuous F)
    (hcharts : ∀ x : X, ∃ (S : Set X) (T : Set Y) (h : S ≃ₜ T),
      (∀ y : S, F y = (h y : Y)) ∧ x ∈ interior S ∧ F x ∈ interior T) :
    IsLocalHomeomorph F := by
  intro x
  obtain ⟨S,T,h,hagree,hx,hFx⟩ := hcharts x
  exact exists_openPartialHomeomorph_of_carrier_homeomorph F hF S T h hagree x hx hFx

end
end SpectreGeometry.ReverseExistence
