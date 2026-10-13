module

public import PrimeFacetClosure.NativeFreeOrbit

@[expose] public section

/-! Every prescribed root site, not just a selected canonical frame, has a
literal full-orbit mate on each registered matching carrier facet. -/
namespace PhysicalRegistration.NativeChair
noncomputable section

 theorem exists_siteTransport_prescribed_root {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (u : Site m) (g : Facet m)
    (hc : poseIsometry q (facetCenter g) = facetCenter u.1)
    (hn : placedNormal (poseIsometry q) (outward g) = -outward u.1) :
    ∃ v : Site m, v.1 = g ∧ SiteTransport (poseIsometry q) u v := by
  have hjk := normal_index_of_facet_normals q u.1 g hn
  let t := tangentRowPermutation q.frame (normalIndex u.1) (normalIndex g) hjk
  let v : Site m := (g, u.2.1.trans t,
    fun j => xor (u.2.2 j) (q.frame.negative ((normalIndex u.1).succAbove (u.2.1 j))))
  have ht : ∀ j, placedNormal (poseIsometry q) (siteAxis v j) = siteAxis u j := by
    intro j
    ext i
    rw [placedNormal_poseIsometry_apply]
    have hp := tangentRowPermutation_axis q.frame (normalIndex u.1) (normalIndex g) hjk (u.2.1 j)
    have he : q.frame.perm i = q.frame.perm ((normalIndex u.1).succAbove (u.2.1 j)) ↔
        i = (normalIndex u.1).succAbove (u.2.1 j) :=
      (rowPermutation q.frame).injective.eq_iff
    by_cases hij : i = (normalIndex u.1).succAbove (u.2.1 j)
    · subst i
      cases hb : q.frame.negative ((normalIndex u.1).succAbove (u.2.1 j)) <;>
        cases hu : u.2.2 j <;>
        simp [v,t,siteAxis,tangentAxis,hp,sign,RegisteredPrime.RegisteredFrame.sign,hb,hu]
    · have hpi : q.frame.perm i ≠ q.frame.perm ((normalIndex u.1).succAbove (u.2.1 j)) :=
        fun h => hij (he.mp h)
      cases hb : q.frame.negative ((normalIndex u.1).succAbove (u.2.1 j)) <;>
        cases hu : u.2.2 j <;>
        simp [v,t,siteAxis,tangentAxis,hp,sign,hb,hu,hpi,hij]
  have hoff : placedNormal (poseIsometry q) (siteOffset v) = siteOffset u := by
    simp only [siteOffset,placedNormal,map_sum,map_smul]
    exact Finset.sum_congr rfl (fun j _ => congrArg (q0 j • ·) (ht j))
  refine ⟨v,rfl,ht,hn,?_⟩
  change (poseIsometry q).toRealAffineIsometryEquiv (facetCenter g + siteOffset v) =
    facetCenter u.1 + siteOffset u
  rw [affineIsometry_map_add]
  change poseIsometry q (facetCenter g) + placedNormal (poseIsometry q) (siteOffset v) = _
  rw [hc,hoff]

#print axioms exists_siteTransport_prescribed_root
end
end PhysicalRegistration.NativeChair
