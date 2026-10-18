module

public import ProductClosure.NativeCompiler
public import ProductClosure.CarrierLocal
public import PhysicalRegistration.TubeSeparation

@[expose] public section

/-!
Native-site instantiation of the exact coordinate tube separation estimates.
All tube sets here are the actual `NativeChair.closedTube` definitions.
-/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration
open scoped InnerProductSpace
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

/-- Exact coordinate data of the exposed polycube facet. -/
def facetPlane (f : Facet S) : ℤ := Polycube.facetPlane f
def facetCellCoordinate (f : Facet S) (k : Fin (m + 1)) : ℤ := f.cell.val k

theorem facetCenter_normal (f : Facet S) :
    facetCenter f (normalIndex f) = (facetPlane f : ℝ) :=
  Polycube.facetCenter_normal f

theorem facetCenter_tangent (f : Facet S) (k : Fin (m + 1))
    (hk : k ≠ normalIndex f) :
    facetCenter f k = (facetCellCoordinate f k : ℝ) + 1 / 2 :=
  Polycube.facetCenter_tangent f k hk

theorem siteCenter_normal  (u : Site S) :
    siteCenter u (normalIndex u.1) = (facetPlane u.1 : ℝ) := by
  simp only [siteCenter, PiLp.add_apply, siteOffset_normal, add_zero, facetCenter_normal]

theorem siteCenter_tangent  (u : Site S) (k : Fin (m + 1))
    (hk : k ≠ normalIndex u.1) :
    siteCenter u k = (facetCellCoordinate u.1 k : ℝ) + 1 / 2 + siteOffset u k := by
  simp only [siteCenter, PiLp.add_apply, facetCenter_tangent u.1 k hk]

/-- The exact asymmetric native tube lies in its symmetric ambient-coordinate
 enclosure; this includes every boundary point of the closed footprint. -/
theorem closedTube_mem_coordinateTube {J : ℕ} (u : Site S) (x : Space m)
    (hx : x ∈ closedTube J u) :
    (fun k => x k) ∈ coordinateTube (normalIndex u.1) (fun k => siteCenter u k)
      (eta m) (rho m) := by
  refine ⟨?_, ?_⟩
  · have hn : |normalCoord u x| = |x (normalIndex u.1) - siteCenter u (normalIndex u.1)| := by
      simp [normalCoord, outward_inner_coordinate, abs_mul]
    simpa only [hn] using hx.1
  · intro k hk
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hk
    let l : Fin m := u.2.1.symm j
    have hl : u.2.1 l = j := u.2.1.apply_symm_apply j
    have hpMinus : 1 ≤ pMinus J l := by
      unfold pMinus
      exact_mod_cast (keyPrime_prime J (2 * l.val)).one_lt.le
    have hpPlus : 1 ≤ pPlus J l := by
      unfold pPlus
      exact_mod_cast (keyPrime_prime J (2 * l.val + 1)).one_lt.le
    have hbound := closed_asymmetric_footprint_coordinate_bound
      (eta m) (pMinus J l) (pPlus J l) (tangentCoord u x l)
      (eta_pos m).le hpMinus hpPlus (hx.2 l)
    have heq : |tangentCoord u x l| = |x k - siteCenter u k| := by
      simp [tangentCoord, siteAxis_inner_coordinate, abs_mul, hl, hj]
    simpa only [heq] using hbound

/-- Transfer a proved coordinate-enclosure separation to actual native tubes. -/
theorem closedTube_disjoint_of_coordinate_enclosures {J : ℕ} (u v : Site S)
    (hsep : Disjoint
      (coordinateTube (normalIndex u.1) (fun k => siteCenter u k) (eta m) (rho m))
      (coordinateTube (normalIndex v.1) (fun k => siteCenter v k) (eta m) (rho m))) :
    Disjoint (closedTube J u) (closedTube J v) := by
  apply Set.disjoint_left.mpr
  intro x hu hv
  exact Set.disjoint_left.mp hsep (closedTube_mem_coordinateTube u x hu)
    (closedTube_mem_coordinateTube v x hv)

/-- Actual native tubes with different normal axes are disjoint. -/
theorem closedTube_disjoint_of_different_normals {J : ℕ} (hm : 2 ≤ m)
    (u v : Site S) (haxis : normalIndex u.1 ≠ normalIndex v.1) :
    Disjoint (closedTube J u) (closedTube J v) := by
  apply closedTube_disjoint_of_coordinate_enclosures
  exact native_coordinateTube_disjoint_of_different_normals ((m : ℝ) + 1)
    (by exact_mod_cast Nat.succ_le_succ hm) (normalIndex u.1) (normalIndex v.1)
    _ _ haxis (facetPlane v.1) (siteCenter_normal v)
    (facetCellCoordinate u.1 (normalIndex v.1)) (siteOffset u (normalIndex v.1))
    (siteCenter_tangent u _ (Ne.symm haxis)) (siteOffset_coordinate_bound u _)

/-- Actual native tubes on distinct parallel facet planes are disjoint. -/
theorem closedTube_disjoint_of_distinct_planes {J : ℕ} (hm : 2 ≤ m)
    (u v : Site S) (haxis : normalIndex u.1 = normalIndex v.1)
    (hplane : facetPlane u.1 ≠ facetPlane v.1) :
    Disjoint (closedTube J u) (closedTube J v) := by
  apply closedTube_disjoint_of_coordinate_enclosures
  have hv : siteCenter v (normalIndex u.1) = (facetPlane v.1 : ℝ) := by
    rw [haxis]; exact siteCenter_normal v
  simpa only [haxis, eta, rho] using
    native_coordinateTube_disjoint_of_distinct_integer_planes ((m : ℝ) + 1)
      (by exact_mod_cast Nat.succ_le_succ hm) (normalIndex u.1)
      (fun k => siteCenter u k) (fun k => siteCenter v k)
      (facetPlane u.1) (facetPlane v.1) (siteCenter_normal u) hv hplane

/-- Actual native tubes on different coplanar unit facets are separated by
any differing tangent cell coordinate. -/
theorem closedTube_disjoint_of_distinct_tangent_cells {J : ℕ} (hm : 2 ≤ m)
    (u v : Site S) (haxis : normalIndex u.1 = normalIndex v.1)
    (k : Fin (m + 1)) (hk : k ≠ normalIndex u.1)
    (hcell : facetCellCoordinate u.1 k ≠ facetCellCoordinate v.1 k) :
    Disjoint (closedTube J u) (closedTube J v) := by
  apply closedTube_disjoint_of_coordinate_enclosures
  have hk' : k ≠ normalIndex v.1 := by simpa only [← haxis] using hk
  simpa only [haxis, eta, rho] using
    native_coordinateTube_disjoint_of_distinct_tangent_cells ((m : ℝ) + 1)
      (by exact_mod_cast Nat.succ_le_succ hm) (normalIndex u.1) k
      (fun j => siteCenter u j) (fun j => siteCenter v j) hk
      (facetCellCoordinate u.1 k) (facetCellCoordinate v.1 k)
      (siteOffset u k) (siteOffset v k)
      (siteCenter_tangent u k hk) (siteCenter_tangent v k hk') hcell
      (siteOffset_coordinate_bound u k) (siteOffset_coordinate_bound v k)

/-- The signed integer numerator carried by an ambient tangent coordinate.
The absolute value remembers the source column, while its sign remembers the
column reversal. -/
def orbitNumerator  (A : Frame m) (k : Fin m) : ℤ :=
  if A.2 (A.1.symm k) then ((A.1.symm k).val : ℤ) + 1
    else -(((A.1.symm k).val : ℤ) + 1)

@[simp] theorem orbitNumerator_natAbs  (A : Frame m) (k : Fin m) :
    (orbitNumerator A k).natAbs = (A.1.symm k).val + 1 := by
  have hcast : ((A.1.symm k).val : ℤ) + 1 = (((A.1.symm k).val + 1 : ℕ) : ℤ) := by
    simp
  simp only [orbitNumerator, hcast]
  split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]

/-- Freeness of the specified signed-permutation orbit, proved from the
positive, pairwise distinct integer magnitudes 1,...,m. -/
theorem orbitNumerator_injective  :
    Function.Injective (fun A : Frame m => orbitNumerator A) := by
  intro A B h
  have hsymm : A.1.symm = B.1.symm := by
    ext k
    have hk := congrArg Int.natAbs (congrFun h k)
    simp only [orbitNumerator_natAbs] at hk
    omega
  have hperm : A.1 = B.1 := by
    simpa only [Equiv.symm_symm] using congrArg Equiv.symm hsymm
  apply Prod.ext hperm
  funext j
  have hnum := congrFun h (A.1 j)
  have hs : B.1.symm (A.1 j) = j := by rw [hperm]; simp
  simp only [orbitNumerator, Equiv.symm_apply_apply, hs] at hnum
  cases ha : A.2 j <;> cases hb : B.2 j <;> try rfl
  · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at hnum
    omega
  · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at hnum
    omega

theorem siteOffset_eq_orbitNumerator  (u : Site S) (k : Fin m) :
    siteOffset u ((normalIndex u.1).succAbove k) =
      (orbitNumerator u.2 k : ℝ) / (4 * ((m : ℝ) + 1)) := by
  have h := siteOffset_tangent u (u.2.1.symm k)
  simp only [Equiv.apply_symm_apply] at h
  rw [h]
  cases hb : u.2.2 (u.2.1.symm k) with
  | false => simp [orbitNumerator, q0, sign, hb]; ring
  | true => simp [orbitNumerator, q0, sign, hb]

/-- Two distinct tangent frames on the same native facet produce disjoint
actual asymmetric tubes. No orbit-freeness hypothesis is supplied. -/
theorem closedTube_disjoint_on_same_facet {J : ℕ} (hm : 2 ≤ m)
    (f : Facet S) (A B : Frame m) (hAB : A ≠ B) :
    Disjoint (closedTube J (f, A)) (closedTube J (f, B)) := by
  have hnum : orbitNumerator A ≠ orbitNumerator B :=
    fun h => hAB (orbitNumerator_injective h)
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hnum
  apply closedTube_disjoint_of_coordinate_enclosures
  apply native_coordinateTube_disjoint_of_distinct_orbit_coordinates
    ((m : ℝ) + 1) (by exact_mod_cast Nat.succ_le_succ hm)
    (normalIndex f) ((normalIndex f).succAbove k)
    (fun j => siteCenter (f, A) j) (fun j => siteCenter (f, B) j)
    (Fin.succAbove_ne _ _) (facetCenter f ((normalIndex f).succAbove k))
    (orbitNumerator A k) (orbitNumerator B k)
  · change facetCenter f _ + siteOffset (f, A) _ = _
    rw [siteOffset_eq_orbitNumerator (f, A) k]
  · change facetCenter f _ + siteOffset (f, B) _ = _
    rw [siteOffset_eq_orbitNumerator (f, B) k]
  · exact hk


/-- Geometric coordinate data identifies the actual exposed polycube facet. -/
theorem facet_eq_of_coordinate_data (f g : Facet S)
    (haxis : normalIndex f = normalIndex g)
    (hplane : facetPlane f = facetPlane g)
    (hcell : ∀ k, k ≠ normalIndex f → facetCellCoordinate f k = facetCellCoordinate g k) :
    f = g := Polycube.facet_eq_of_coordinates f g haxis hplane hcell

/-- Any two different indexed native sites have disjoint closed tubes.
This is a theorem about the literal finite keyed-polycube construction. -/
theorem closedTube_pairwise_disjoint {J : ℕ} (hm : 2 ≤ m) :
    Pairwise (fun u v : Site S => Disjoint (closedTube J u) (closedTube J v)) := by
  intro u v huv
  by_cases haxis : normalIndex u.1 = normalIndex v.1
  · by_cases hplane : facetPlane u.1 = facetPlane v.1
    · by_cases hcell : ∀ k, k ≠ normalIndex u.1 →
          facetCellCoordinate u.1 k = facetCellCoordinate v.1 k
      · have hfacet := facet_eq_of_coordinate_data u.1 v.1 haxis hplane hcell
        rcases u with ⟨f, A⟩
        rcases v with ⟨g, B⟩
        change f = g at hfacet
        subst g
        apply closedTube_disjoint_on_same_facet hm f A B
        intro hAB
        exact huv (by simp only [hAB])
      · push Not at hcell
        obtain ⟨k, hk, hc⟩ := hcell
        exact closedTube_disjoint_of_distinct_tangent_cells hm u v haxis k hk hc
    · exact closedTube_disjoint_of_distinct_planes hm u v haxis hplane
  · exact closedTube_disjoint_of_different_normals hm u v haxis


end
end ProductClosure.NativeCompiler
