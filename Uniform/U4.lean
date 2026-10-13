module

public import Uniform.U3
public import Uniform.U2

@[expose] public section

/-! U4: covariance identities of `Λ(μ, g)` for every prime `p`:
translation `f_(A+1)(i) = f_A(i-1)` and the scalar identity `Q h_(Q⁻¹A) Q⁻¹ = h_A`. -/
namespace Uniform

theorem filter_sum_eq (l : List Nat) (B : Nat → Bool) :
    (l.filter B).sum = (l.map (fun j => if B j then j else 0)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases B a <;> simp [ih]

theorem natCast_sum (l : List Nat) (f : Nat → Nat) :
    (((l.map f).sum : Nat) : Int) = (l.map (fun x => (f x : Int))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, Int.natCast_add, ih]

theorem MEq.sum_map {p : Nat} {α : Type} (l : List α) (f g : α → Int)
    (h : ∀ x ∈ l, MEq p (f x) (g x)) : MEq p (l.map f).sum (l.map g).sum := by
  induction l with
  | nil => exact MEq.refl _
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem sum_affine_ident (l : List Nat) (A : Nat → Bool) (c1 c0 : Int) :
    (l.map (fun i => if A i then c1 * (i : Int) + c0 else 0)).sum
      = c1 * (((l.filter A).sum : Nat) : Int) + c0 * ((l.countP A : Nat) : Int) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons, List.countP_cons, ih]
    cases A a <;> simp <;> grind

/-- reindexing a support sum along a permutation `σ` with left inverse `τ` -/
theorem suppSum_reindex {p : Nat} {σ τ : Nat → Nat} (hσ : IsPermOn p σ)
    (hτσ : ∀ i, i < p → τ (σ i) = i) (A : Nat → Bool) :
    suppSum p (fun j => A (τ j)) = ((List.range p).map (fun i => if A i then σ i else 0)).sum := by
  unfold suppSum
  rw [filter_sum_eq, ← sum_comp_perm hσ]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [hτσ i (List.mem_range.1 hi)]

theorem suppSum_affine {p : Nat} {σ τ : Nat → Nat} (hσ : IsPermOn p σ)
    (hτσ : ∀ i, i < p → τ (σ i) = i) (A : Nat → Bool) {c1 c0 : Int}
    (haff : ∀ i, i < p → MEq p (σ i) (c1 * i + c0)) :
    MEq p (suppSum p (fun j => A (τ j))) (c1 * (suppSum p A : Int) + c0 * (suppCard p A : Int)) := by
  rw [suppSum_reindex hσ hτσ A, natCast_sum]
  have := MEq.sum_map (p := p) (List.range p)
    (fun i => ((if A i then σ i else 0 : Nat) : Int))
    (fun i => if A i then c1 * (i : Int) + c0 else 0)
    (fun i hi => by
      cases A i
      · exact MEq.refl _
      · exact haff i (List.mem_range.1 hi))
  rw [sum_affine_ident] at this
  exact this

theorem nonemptyProper_reindex {p : Nat} {σ τ : Nat → Nat} (hσ : IsPermOn p σ)
    (hτσ : ∀ i, i < p → τ (σ i) = i) {A : Nat → Bool} (hA : NonemptyProperOn p A) :
    NonemptyProperOn p (fun j => A (τ j)) := by
  obtain ⟨⟨i1, h1p, h1⟩, ⟨i0, h0p, h0⟩⟩ := hA
  exact ⟨⟨σ i1, hσ.1 _ h1p, by simp only [hτσ i1 h1p, h1]⟩,
         ⟨σ i0, hσ.1 _ h0p, by simp only [hτσ i0 h0p, h0]⟩⟩

theorem suppCard_reindex {p : Nat} {σ τ : Nat → Nat} (hσ : IsPermOn p σ)
    (hτσ : ∀ i, i < p → τ (σ i) = i) (A : Nat → Bool) :
    suppCard p (fun j => A (τ j)) = suppCard p A := by
  unfold suppCard
  rw [← countP_comp_perm hσ]
  apply countP_congr_range
  intro i hi; simp only [hτσ i hi]

/-- the mean moves affinely: `z_B ≡ c1 z_A + c0` -/
theorem zA_affine {p : Nat} (hp : IsPrime p) {σ τ : Nat → Nat} (hσ : IsPermOn p σ)
    (hτσ : ∀ i, i < p → τ (σ i) = i) {A : Nat → Bool} (hA : NonemptyProperOn p A) {c1 c0 : Int}
    (haff : ∀ i, i < p → MEq p (σ i) (c1 * i + c0)) :
    MEq p (zA p (fun j => A (τ j))) (c1 * (zA p A : Int) + c0) := by
  have hB := nonemptyProper_reindex hσ hτσ hA
  have hk := suppCard_reindex hσ hτσ A
  obtain ⟨_, hzA, _⟩ := U1_zA p hp A hA
  obtain ⟨_, hzB, _⟩ := U1_zA p hp _ hB
  rw [hk] at hzB
  have hS := suppSum_affine hσ hτσ A haff
  have eA := MEq.of_nat_mod hzA
  have eB := MEq.of_nat_mod hzB
  simp only [Int.natCast_mul] at eA eB
  -- k z_B ≡ S_B ≡ c1 S_A + c0 k ≡ c1 k z_A + c0 k = (c1 z_A + c0) k
  have h1 : MEq p ((zA p (fun j => A (τ j)) : Int) * (suppCard p A : Int))
      ((c1 * (zA p A : Int) + c0) * (suppCard p A : Int)) := by
    have := eB.trans (hS.trans ((MEq.refl c1).mul eA.symm |>.add (MEq.refl (c0 * (suppCard p A : Int)))))
    exact (MEq.of_eq (by grind)).trans (this.trans (MEq.of_eq (by grind)))
  have hkd : ¬ p ∣ suppCard p A := by
    have := suppCard_bounds hA
    exact IsPrime.not_dvd_of_pos_lt (by omega) this.2
  exact h1.cancel hp (int_not_dvd hkd)

theorem shift_left_inv {p : Nat} (hp : 0 < p) (i : Nat) (hi : i < p) :
    ((i + 1) % p + p - 1) % p = i := by
  by_cases h : i + 1 < p
  · rw [Nat.mod_eq_of_lt h, show i + 1 + p - 1 = i + p by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  · have e : i + 1 = p := by omega
    rw [e, Nat.mod_self, show 0 + p - 1 = i by omega, Nat.mod_eq_of_lt hi]

/-- **U4 (translation).** `f_(A+1)(i) = f_A(i - 1)`. -/
theorem U4_translation (p mu g : Nat) (hp : IsPrime p) (A : Nat → Bool)
    (hA : NonemptyProperOn p A) (i : Nat) (hi : i < p) :
    lamPerm p mu g (shiftSupp p A) i = lamPerm p mu g A ((i + p - 1) % p) := by
  have h2 := hp.two_le
  let σ : Nat → Nat := fun i => (i + 1) % p
  let τ : Nat → Nat := fun j => (j + p - 1) % p
  have hσaff : ∀ i, i < p → MEq p (σ i) (1 * (i : Int) + 1) := by
    intro i _
    simp only [σ, Int.natCast_emod, Int.natCast_add, Int.one_mul]
    exact MEq.emod_self _
  have hσ : IsPermOn p σ :=
    affine_perm hp (fun i _ => Nat.mod_lt _ (by omega)) (m := 1)
      (IsPrime.not_dvd_of_pos_lt (by omega) (by omega)) (by simpa using hσaff)
  have hτσ : ∀ i, i < p → τ (σ i) = i := fun i hi => shift_left_inv (by omega) i hi
  have hB : shiftSupp p A = fun j => A (τ j) := rfl
  have hk : suppCard p (shiftSupp p A) = suppCard p A := suppCard_reindex hσ hτσ A
  have hz : MEq p (zA p (shiftSupp p A)) (1 * (zA p A : Int) + 1) := zA_affine hp hσ hτσ hA hσaff
  have hBA : NonemptyProperOn p (shiftSupp p A) := nonemptyProper_reindex hσ hτσ hA
  have hzB := (U1_zA p hp _ hBA).1
  have hzA := (U1_zA p hp A hA).1
  have e1 := lamPerm_affine p mu g (shiftSupp p A) (by omega) i
  have e2 := lamPerm_affine p mu g A (by omega) ((i + p - 1) % p)
  rw [hk] at e1
  generalize ((mu * g ^ suppCard p A : Nat) : Int) = m at e1 e2
  have hj : MEq p (((i + p - 1) % p : Nat) : Int) ((i : Int) - 1) := by
    rw [Int.natCast_emod]
    refine (MEq.emod_self _).trans ⟨1, ?_⟩
    have : ((i + p - 1 : Nat) : Int) = (i : Int) + p - 1 := by omega
    rw [this]; omega
  have hmid : MEq p (m * (i : Int) + m * ((p : Int) - (zA p (shiftSupp p A) : Int)))
      (m * (((i + p - 1) % p : Nat) : Int) + m * ((p : Int) - (zA p A : Int))) := by
    have a1 := (MEq.refl (m * (i : Int))).add ((MEq.refl m).mul ((MEq.refl (p : Int)).sub hz))
    have a2 := ((MEq.refl m).mul hj.symm).add (MEq.refl (m * ((p : Int) - (zA p A : Int))))
    exact a1.trans ((MEq.of_eq (by grind)).trans a2)
  have := (e1.trans (hmid.trans e2.symm)).eq_of_lt (by omega)
    (by have := lamPerm_lt p mu g (by omega) (shiftSupp p A) i; omega) (by omega)
    (by have := lamPerm_lt p mu g (by omega) A ((i + p - 1) % p); omega)
  omega

/-- **U4 (scalar covariance).** For `ρ ρ' ≡ 1`, `Q = M_ρ`: `Q h_(ρA) Q⁻¹ = h_A` as frames. -/
theorem U4_square_scalar (p mu g ρ ρ' : Nat) (hp : IsPrime p) (hρ : (ρ * ρ') % p = 1)
    (A : Nat → Bool) (hA : NonemptyProperOn p A) (i : Nat) (hi : i < p) :
    (((scalarFrame p ρ).comp (lamChild p mu g (scaleSupp p ρ' A))).comp (scalarFrame p ρ')).perm i
        = (lamChild p mu g A).perm i ∧
    (((scalarFrame p ρ).comp (lamChild p mu g (scaleSupp p ρ' A))).comp (scalarFrame p ρ')).neg i
        = (lamChild p mu g A).neg i := by
  have h2 := hp.two_le
  have hρρ : MEq p ((ρ : Int) * ρ') 1 := by
    have := MEq.of_nat_mod (p := p) (a := ρ * ρ') (b := 1) (by rw [hρ, Nat.mod_eq_of_lt (by omega)])
    simp only [Int.natCast_mul] at this
    exact this
  have hρd : ¬ p ∣ ρ := by
    intro hd
    have : p ∣ ρ * ρ' := Nat.dvd_trans hd (Nat.dvd_mul_right ρ ρ')
    rw [Nat.mod_eq_zero_of_dvd this] at hρ; exact absurd hρ (by decide)
  let σ : Nat → Nat := fun i => (ρ * i) % p
  let τ : Nat → Nat := fun j => (ρ' * j) % p
  have hσ : IsPermOn p σ := mulMap_perm hp hρd
  have hσaff : ∀ i, i < p → MEq p (σ i) ((ρ : Int) * i + 0) := by
    intro i _
    simp only [σ, Int.natCast_emod, Int.natCast_mul, Int.add_zero]
    exact MEq.emod_self _
  have hτσ : ∀ i, i < p → τ (σ i) = i := by
    intro i hi
    have hm : MEq p ((τ (σ i) : Nat) : Int) (i : Int) := by
      simp only [τ, σ, Int.natCast_emod, Int.natCast_mul]
      refine (MEq.emod_self _).trans ?_
      have := (MEq.refl (ρ' : Int)).mul (MEq.emod_self (p := p) ((ρ : Int) * i))
      refine this.trans ?_
      have := hρρ.mul (MEq.refl (i : Int))
      exact (MEq.of_eq (by grind)).trans (this.trans (MEq.of_eq (by grind)))
    exact (hm.eq_of_lt (by omega) (by have := Nat.mod_lt (ρ' * ((ρ * i) % p)) (show 0 < p by omega); simp only [τ, σ]; omega)
      (by omega) (by omega)) |> fun h => by omega
  have hC : scaleSupp p ρ' A = fun j => A (τ j) := rfl
  refine ⟨?_, ?_⟩
  · -- permutation part
    have hk : suppCard p (scaleSupp p ρ' A) = suppCard p A := suppCard_reindex hσ hτσ A
    have hz : MEq p (zA p (scaleSupp p ρ' A)) ((ρ : Int) * (zA p A : Int) + 0) :=
      zA_affine hp hσ hτσ hA hσaff
    have hCA : NonemptyProperOn p (scaleSupp p ρ' A) := nonemptyProper_reindex hσ hτσ hA
    have hzC := (U1_zA p hp _ hCA).1
    have hzA := (U1_zA p hp A hA).1
    simp only [Frame.comp, scalarFrame, lamChild]
    have e1 := lamPerm_affine p mu g (scaleSupp p ρ' A) (by omega) ((ρ * i) % p)
    have e2 := lamPerm_affine p mu g A (by omega) i
    rw [hk] at e1
    generalize ((mu * g ^ suppCard p A : Nat) : Int) = m at e1 e2
    have hlhs : MEq p ((((ρ' * lamPerm p mu g (scaleSupp p ρ' A) ((ρ * i) % p)) % p : Nat) : Int))
        ((ρ' : Int) * (m * (((ρ * i) % p : Nat) : Int)
          + m * ((p : Int) - (zA p (scaleSupp p ρ' A) : Int)))) := by
      rw [Int.natCast_emod, Int.natCast_mul]
      exact (MEq.emod_self _).trans ((MEq.refl (ρ' : Int)).mul e1)
    have hρi : MEq p (((ρ * i) % p : Nat) : Int) ((ρ : Int) * i) := by
      rw [Int.natCast_emod, Int.natCast_mul]; exact MEq.emod_self _
    have step1 : MEq p ((ρ' : Int) * (m * (((ρ * i) % p : Nat) : Int)
          + m * ((p : Int) - (zA p (scaleSupp p ρ' A) : Int))))
        ((ρ' : Int) * (m * ((ρ : Int) * i) + m * ((p : Int) - ((ρ : Int) * (zA p A : Int) + 0)))) :=
      (MEq.refl (ρ' : Int)).mul (((MEq.refl m).mul hρi).add
        ((MEq.refl m).mul ((MEq.refl (p : Int)).sub hz)))
    have step2 : MEq p ((ρ' : Int) * (m * ((ρ : Int) * i) + m * ((p : Int) - ((ρ : Int) * (zA p A : Int) + 0))))
        (((ρ : Int) * ρ') * (m * i - m * (zA p A : Int)) + (p : Int) * (ρ' * m)) :=
      MEq.of_eq (by grind)
    have step3 : MEq p (((ρ : Int) * ρ') * (m * i - m * (zA p A : Int)) + (p : Int) * (ρ' * m))
        (1 * (m * i - m * (zA p A : Int)) + (p : Int) * m) :=
      (hρρ.mul (MEq.refl _)).add
        ((MEq.zero_of_dvd (Int.dvd_mul_right _ _)).trans (MEq.zero_of_dvd (Int.dvd_mul_right _ _)).symm)
    have step4 : MEq p (1 * (m * i - m * (zA p A : Int)) + (p : Int) * m)
        (m * (i : Int) + m * ((p : Int) - (zA p A : Int))) := MEq.of_eq (by grind)
    have hall := hlhs.trans (step1.trans (step2.trans (step3.trans (step4.trans e2.symm))))
    have := hall.eq_of_lt (by omega)
      (by have := Nat.mod_lt (ρ' * lamPerm p mu g (scaleSupp p ρ' A) ((ρ * i) % p)) (show 0 < p by omega); omega)
      (by omega) (by have := lamPerm_lt p mu g (by omega) A i; omega)
    omega
  · -- sign part
    simp only [Frame.comp, scalarFrame, lamChild, scaleSupp, Bool.false_xor, Bool.xor_false]
    have := hτσ i hi
    simp only [τ, σ] at this
    rw [this]

end Uniform
