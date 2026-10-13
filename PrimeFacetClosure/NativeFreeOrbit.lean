module

public import PrimeFacetClosure.NativeFacetGeometry

@[expose] public section

/-! Completion of every matched registered carrier facet to a literal pair
of sites in the full, unquotiented signed-permutation tangent orbit. -/
namespace PhysicalRegistration.NativeChair
noncomputable section
open RegisteredPrime.PrimeFacetClosure

/-- The registered index permutation restricted to the two tangent index sets. -/
def tangentRowPermutation {m : ℕ} (F : RegisteredPrime.RegisteredFrame (m+1))
    (j k : Fin (m+1)) (hjk : F.perm j = k) : Equiv.Perm (Fin m) :=
  (finSuccAboveEquiv j).trans
    ((Equiv.subtypeEquiv (rowPermutation F) (fun i => by
      change i ≠ j ↔ F.perm i ≠ k
      rw [← hjk]
      exact (rowPermutation F).injective.ne_iff.symm)).trans (finSuccAboveEquiv k).symm)

@[simp] theorem tangentRowPermutation_axis {m : ℕ}
    (F : RegisteredPrime.RegisteredFrame (m+1)) (j k : Fin (m+1))
    (hjk : F.perm j = k) (i : Fin m) :
    k.succAbove (tangentRowPermutation F j k hjk i) = F.perm (j.succAbove i) := by
  let e : {i : Fin (m+1) // i ≠ j} ≃ {i : Fin (m+1) // i ≠ k} := Equiv.subtypeEquiv (rowPermutation F) (fun i => by
    change i ≠ j ↔ F.perm i ≠ k
    rw [← hjk]
    exact (rowPermutation F).injective.ne_iff.symm)
  have h := (finSuccAboveEquiv k).apply_symm_apply (e (finSuccAboveEquiv j i))
  exact congrArg Subtype.val h

/-- Opposite actual normals identify the source coordinate normal axis. -/
theorem normal_index_of_facet_normals {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (f g : Facet m) (hn : placedNormal (poseIsometry q) (outward g) = -outward f) :
    q.frame.perm (normalIndex f) = normalIndex g := by
  by_contra hi
  have hh := congrArg (fun x : Space m => x (normalIndex f)) hn
  rw [placedNormal_poseIsometry_apply] at hh
  have hnz : normalSign f ≠ 0 := by
    intro hz
    have ha := abs_normalSign f
    rw [hz, abs_zero] at ha
    norm_num at ha
  apply hnz
  simpa [outward, PiLp.smul_apply, hi] using hh

/-- There really is a pair of full free-orbit sites on every matched pair
of registered facets. No compiler coefficient, profile legality or graph
path is assumed; this constructs the needed site frames explicitly. -/
theorem exists_siteTransport_of_facet_match {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (f g : Facet m) (hc : poseIsometry q (facetCenter g) = facetCenter f)
    (hn : placedNormal (poseIsometry q) (outward g) = -outward f) :
    ∃ u v : Site m, u.1 = f ∧ v.1 = g ∧ SiteTransport (poseIsometry q) u v := by
  have hjk := normal_index_of_facet_normals q f g hn
  let u : Site m := (f, Equiv.refl _, fun _ => true)
  let v : Site m := (g, tangentRowPermutation q.frame (normalIndex f) (normalIndex g) hjk,
    fun i => !(q.frame.negative ((normalIndex f).succAbove i)))
  have ht : ∀ j, placedNormal (poseIsometry q) (siteAxis v j) = siteAxis u j := by
    intro j
    ext i
    rw [placedNormal_poseIsometry_apply]
    have hp := tangentRowPermutation_axis q.frame (normalIndex f) (normalIndex g) hjk j
    have he : q.frame.perm i = q.frame.perm ((normalIndex f).succAbove j) ↔
        i = (normalIndex f).succAbove j := by
      exact (rowPermutation q.frame).injective.eq_iff
    by_cases hij : i = (normalIndex f).succAbove j
    · subst i
      cases hb : q.frame.negative ((normalIndex f).succAbove j) <;>
        simp [v, u, siteAxis, tangentAxis, hp, sign,
          RegisteredPrime.RegisteredFrame.sign, hb]
    · have hpi : q.frame.perm i ≠ q.frame.perm ((normalIndex f).succAbove j) :=
        fun h => hij (he.mp h)
      cases hb : q.frame.negative ((normalIndex f).succAbove j) <;>
        simp [v, u, siteAxis, tangentAxis, hp, sign, hb, hpi, hij]
  have hoff : placedNormal (poseIsometry q) (siteOffset v) = siteOffset u := by
    simp only [siteOffset, placedNormal, map_sum, map_smul]
    exact Finset.sum_congr rfl (fun j _ => congrArg (q0 j • ·) (ht j))
  refine ⟨u, v, rfl, rfl, ht, hn, ?_⟩
  change (poseIsometry q).toRealAffineIsometryEquiv (facetCenter g + siteOffset v) =
    facetCenter f + siteOffset u
  rw [affineIsometry_map_add]
  change poseIsometry q (facetCenter g) + placedNormal (poseIsometry q) (siteOffset v) = _
  rw [hc, hoff]

#print axioms tangentRowPermutation_axis
#print axioms exists_siteTransport_of_facet_match
end
end PhysicalRegistration.NativeChair
