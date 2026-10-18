module

public import PrimeFacetClosure.NativeFreeOrbit
public import ProductClosure.MaterialCovariance
public import ProductClosure.MatchedLatticeCells

@[expose] public section

/-! Every prescribed root site, not just a selected canonical frame, has a
literal full-orbit mate on each registered matching carrier facet. -/
namespace ProductClosure.NativeCompiler
noncomputable section
open PhysicalRegistration PhysicalRegistration.NativeChair
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}


theorem poseIsometry_map_latticeCenter (q : RegisteredPrime.Pose (m + 1))
    (z : LatticeIndex m) : poseIsometry q (latticeCenter z) = latticeCenter (q.cell z) := by
  exact (poseIsometry_realizes q).map_latticeCenter z

theorem placedNormal_poseIsometry_apply (q : RegisteredPrime.Pose (m + 1))
    (x : Space m) (i : Fin (m + 1)) :
    placedNormal (poseIsometry q) x i = (q.frame.sign i : ℝ) * x (q.frame.perm i) := by
  exact PhysicalRegistration.NativeChair.placedNormal_poseIsometry_apply q x i

theorem normal_index_of_facet_normals (q : RegisteredPrime.Pose (m+1))
    (f g : Facet S) (hn : placedNormal (poseIsometry q) (outward g) = -outward f) :
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

 theorem exists_siteTransport_prescribed_root  (q : RegisteredPrime.Pose (m+1))
    (u : Site S) (g : Facet S)
    (hc : poseIsometry q (facetCenter g) = facetCenter u.1)
    (hn : placedNormal (poseIsometry q) (outward g) = -outward u.1) :
    ∃ v : Site S, v.1 = g ∧ SiteTransport (poseIsometry q) u v := by
  have hjk := normal_index_of_facet_normals q u.1 g hn
  let t := tangentRowPermutation q.frame (normalIndex u.1) (normalIndex g) hjk
  let v : Site S := (g, u.2.1.trans t,
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
end ProductClosure.NativeCompiler
