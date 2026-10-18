module

public import SpectreGeometry.PolygonProductKeyPacking
public import Mathlib.Analysis.Convex.Topology

@[expose] public section


/-! Dense finite affine-plane avoidance, specialized to actual Euclidean4.
This reusable step supplies properness witnesses by a finite containment
filter. It assumes no geometric classification of tile contacts. -/
namespace SpectreGeometry.ProductCrease
noncomputable section
open Set
open scoped InnerProductSpace

def avoidsAffinePlanes {ι : Type*} (I : Finset ι)
    (n : ι → EFour) (c : ι → ℝ) : Set EFour :=
  {x | ∀ i ∈ I, inner ℝ (n i) x ≠ c i}

theorem convex_subset_closure_avoid_plane (C : Set EFour)
    (hC : Convex ℝ C) (n : EFour) (c : ℝ)
    (hproper : ∃ y ∈ C, inner ℝ n y ≠ c) :
    C ⊆ closure (C ∩ {x | inner ℝ n x ≠ c}) := by
  intro x hx
  by_cases he : inner ℝ n x = c
  · obtain ⟨y,hy,hny⟩ := hproper
    have hsegment : openSegment ℝ x y ⊆ C ∩ {z | inner ℝ n z ≠ c} := by
      rintro z ⟨a,b,ha,hb,hab,rfl⟩
      refine ⟨hC hx hy ha.le hb.le hab,?_⟩
      simp only [mem_setOf_eq,inner_add_right,real_inner_smul_right,he]
      intro h
      have hbalance : (a+b)*c = c := by rw [hab,one_mul]
      have hz : b * (inner ℝ n y-c) = 0 := by nlinarith [hbalance]
      exact hny (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hb.ne'))
    exact (closure_mono hsegment)
      (segment_subset_closure_openSegment (left_mem_segment ℝ x y))
  · exact subset_closure ⟨hx,he⟩

private theorem dense_inter_open (C A V : Set EFour)
    (hA : C ⊆ closure A) (hV : IsOpen V)
    (hCV : C ⊆ closure (C ∩ V)) : C ⊆ closure (A ∩ V) := by
  apply hCV.trans
  have hh : C ∩ V ⊆ closure (A ∩ V) := by
    intro x hx
    exact hV.closure_inter ⟨hA hx.1,hx.2⟩
  exact (closure_mono hh).trans_eq closure_closure

theorem convex_generic_finite_avoidance {ι : Type*}
    (C G : Set EFour) (hC : Convex ℝ C) (hClosed : IsClosed C)
    (hG : closure G = C) (I : Finset ι) (n : ι → EFour) (c : ι → ℝ)
    (hproper : ∀ i ∈ I, ∃ y ∈ C, inner ℝ (n i) y ≠ c i) :
    closure (G ∩ avoidsAffinePlanes I n c) = C := by
  classical
  have hlower : C ⊆ closure (G ∩ avoidsAffinePlanes I n c) := by
    induction I using Finset.induction_on with
    | empty => simp [avoidsAffinePlanes,hG]
    | @insert i I hi ih =>
      have hrest : ∀ j ∈ I, ∃ y ∈ C, inner ℝ (n j) y ≠ c j :=
        fun j hj => hproper j (Finset.mem_insert_of_mem hj)
      have hcurrent : ∃ y ∈ C, inner ℝ (n i) y ≠ c i :=
        hproper i (Finset.mem_insert_self i I)
      have hopen : IsOpen {x : EFour | inner ℝ (n i) x ≠ c i} :=
        (isClosed_eq (by fun_prop) continuous_const).isOpen_compl
      have h := dense_inter_open C (G ∩ avoidsAffinePlanes I n c)
        {x | inner ℝ (n i) x ≠ c i} (ih hrest) hopen
        (convex_subset_closure_avoid_plane C hC (n i) (c i) hcurrent)
      simpa only [avoidsAffinePlanes,Finset.mem_insert,forall_eq_or_imp,
        ofPred_and,inter_assoc,inter_left_comm,inter_comm] using h
  apply subset_antisymm _ hlower
  apply closure_minimal _ hClosed
  intro x hx
  rw [← hG]
  exact subset_closure hx.1

theorem convex_generic_finite_plane_dichotomy {κ : Type*} [Fintype κ]
    (C G : Set EFour) (hC : Convex ℝ C) (hClosed : IsClosed C)
    (hG : closure G = C) (n : κ → EFour) (c : κ → ℝ) :
    ∃ D : Set EFour, D ⊆ G ∧ closure D = C ∧
      ∀ x ∈ D, ∀ k, inner ℝ (n k) x = c k →
        C ⊆ {y | inner ℝ (n k) y = c k} := by
  classical
  let I : Finset κ := Finset.univ.filter (fun k => ∃ y ∈ C, inner ℝ (n k) y ≠ c k)
  let D := G ∩ avoidsAffinePlanes I n c
  have hproper : ∀ k ∈ I, ∃ y ∈ C, inner ℝ (n k) y ≠ c k := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  refine ⟨D,inter_subset_left,
    convex_generic_finite_avoidance C G hC hClosed hG I n c hproper,?_⟩
  intro x hx k hxplane y hy
  by_contra hne
  have hk : k ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ k,y,hy,hne⟩
  exact hx.2 k hk hxplane

end
end SpectreGeometry.ProductCrease
