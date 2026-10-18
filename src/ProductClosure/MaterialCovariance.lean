module

public import ProductClosure.NativeProfileDefinitions

@[expose] public section

/-! Literal material covariance under a complete matched native site frame.
Opposite integer coefficients make the two graph pieces complementary inside
their common real tube; no tiling or material-gluing premise is used. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration
open scoped InnerProductSpace
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

/-- Tangent coordinates are preserved by complete keyed-frame matching. -/
theorem SiteTransport.tangentCoord_map  {e : Space m ≃ᵢ Space m}
    {u v : Site S} (h : SiteTransport e u v) (x : Space m) (j : Fin m) :
    tangentCoord u (e x) j = tangentCoord v x j := by
  have ht := placedNormal_inner_sub e (siteAxis v j) (e x) (e (siteCenter v))
  simp only [IsometryEquiv.symm_apply_apply] at ht
  rw [h.1 j, h.2.2] at ht
  exact ht

/-- Outward normal coordinates reverse across a matched facet. -/
theorem SiteTransport.normalCoord_map  {e : Space m ≃ᵢ Space m}
    {u v : Site S} (h : SiteTransport e u v) (x : Space m) :
    normalCoord u (e x) = -normalCoord v x := by
  have hn := placedNormal_inner_sub e (outward v.1) (e x) (e (siteCenter v))
  simp only [IsometryEquiv.symm_apply_apply] at hn
  rw [h.2.1, h.2.2] at hn
  simp only [inner_neg_left] at hn
  change -normalCoord u (e x) = normalCoord v x at hn
  linarith

/-- Matching transports the complete closed asymmetric tube, not just its base. -/
theorem SiteTransport.closedTube_iff  {e : Space m ≃ᵢ Space m}
    {u v : Site S} (h : SiteTransport e u v) (J : ℕ) (x : Space m) :
    e x ∈ closedTube J u ↔ x ∈ closedTube J v := by
  simp only [closedTube, mem_ofPred_eq, h.normalCoord_map x, abs_neg, h.tangentCoord_map x]

theorem SiteTransport.image_closedTube  {e : Space m ≃ᵢ Space m}
    {u v : Site S} (h : SiteTransport e u v) (J : ℕ) :
    e '' closedTube J v = closedTube J u := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h.closedTube_iff J y).mpr hy
  · intro hx
    exact ⟨e.symm x, (h.closedTube_iff J (e.symm x)).mp (by simpa using hx), by simp⟩

/-- The literal max-min tent profile is identical in matched tangent coordinates. -/
theorem SiteTransport.tentProfile  [NeZero m] {e : Space m ≃ᵢ Space m}
    {u v : Site S} (h : SiteTransport e u v) (J : ℕ) (x : Space m) :
    keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) (e x - siteCenter u) =
      keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis v) (x - siteCenter v) := by
  unfold keyTentProfile finiteLowerEnvelope
  have ht (j : Fin m) : ⟪siteAxis u j, e x - siteCenter u⟫_ℝ =
      ⟪siteAxis v j, x - siteCenter v⟫_ℝ := h.tangentCoord_map x j
  simp_rw [ht]

/-- Opposite actual coefficients give exactly opposite signed graph heights. -/
theorem SiteTransport.siteHeight_neg {J : ℕ} [NeZero m]
    {e : Space m ≃ᵢ Space m} {u v : Site S} (h : SiteTransport e u v)
    (a : Coefficients S J) (hc : a.value v = -a.value u) (x : Space m) :
    siteHeight a v x = -siteHeight a u (e x) := by
  unfold siteHeight keyHeight
  rw [h.tentProfile J x, hc, Int.cast_neg]
  ring

/-- The moved hypograph is precisely the complementary closed side of the
same graph, including the graph itself. -/
theorem SiteTransport.image_siteHypograph {J : ℕ} [NeZero m]
    {e : Space m ≃ᵢ Space m} {u v : Site S} (h : SiteTransport e u v)
    (a : Coefficients S J) (hc : a.value v = -a.value u) :
    e '' siteHypograph a v = {x | siteHeight a u x ≤ normalCoord u x} := by
  ext x
  have hn := h.normalCoord_map (e.symm x)
  have hh := h.siteHeight_neg a hc (e.symm x)
  simp only [IsometryEquiv.apply_symm_apply] at hn hh
  constructor
  · rintro ⟨y, hy, rfl⟩
    change normalCoord v y ≤ siteHeight a v y at hy
    have hn' := h.normalCoord_map y
    have hh' := h.siteHeight_neg a hc y
    change siteHeight a u (e y) ≤ normalCoord u (e y)
    linarith
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    change normalCoord v (e.symm x) ≤ siteHeight a v (e.symm x)
    change siteHeight a u x ≤ normalCoord u x at hx
    linarith

/-- The two actual replacement pieces cover their full common tube. -/
theorem SiteTransport.replacementPiece_union {J : ℕ} [NeZero m]
    {e : Space m ≃ᵢ Space m} {u v : Site S} (h : SiteTransport e u v)
    (a : Coefficients S J) (hc : a.value v = -a.value u) :
    replacementPiece a u ∪ e '' replacementPiece a v = closedTube J u := by
  rw [replacementPiece, replacementPiece, Set.image_inter e.injective,
    h.image_closedTube J, h.image_siteHypograph a hc]
  ext x
  simp only [mem_union, mem_inter_iff, siteHypograph, mem_ofPred_eq]
  constructor
  · exact fun hx => hx.elim And.left And.left
  · intro hx
    rcases le_total (normalCoord u x) (siteHeight a u x) with hh | hh
    · exact Or.inl ⟨hx, hh⟩
    · exact Or.inr ⟨hx, hh⟩

/-- Their overlap is exactly the common graph; no positive material overlap
is concealed in the coefficient equation. -/
theorem SiteTransport.replacementPiece_inter {J : ℕ} [NeZero m]
    {e : Space m ≃ᵢ Space m} {u v : Site S} (h : SiteTransport e u v)
    (a : Coefficients S J) (hc : a.value v = -a.value u) :
    replacementPiece a u ∩ e '' replacementPiece a v = keyGraph a u := by
  rw [replacementPiece, replacementPiece, Set.image_inter e.injective,
    h.image_closedTube J, h.image_siteHypograph a hc]
  ext x
  simp only [mem_inter_iff, siteHypograph, keyGraph, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨ht, hl⟩, _, hr⟩
    exact ⟨ht, le_antisymm hl hr⟩
  · rintro ⟨ht, he⟩
    exact ⟨⟨ht, he.le⟩, ht, he.ge⟩


/-- The complementary graph pieces have genuinely disjoint interiors. -/
theorem SiteTransport.replacementPiece_interiors_disjoint {J : ℕ} [NeZero m]
    (hm : 2 ≤ m) {e : Space m ≃ᵢ Space m} {u v : Site S} (h : SiteTransport e u v)
    (a : Coefficients S J) (hc : a.value v = -a.value u) :
    Disjoint (interior (replacementPiece a u)) (interior (e '' replacementPiece a v)) := by
  letI : Nonempty (Polycube.Cell S) := ⟨u.1.cell⟩
  apply Set.disjoint_iff_inter_eq_empty.mpr
  rw [← interior_inter, h.replacementPiece_inter a hc]
  have hs := interior_mono (keyGraph_subset_frontier_body hm a u)
  rw [interior_frontier (body_isClosed a)] at hs
  exact Set.Subset.antisymm hs (Set.empty_subset _)

end
end ProductClosure.NativeCompiler
