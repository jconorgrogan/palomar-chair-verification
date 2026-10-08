module

public import Uniform.U1
public import Uniform.Sign

@[expose] public section

/-! U3: Zolotarev (sign of `i ↦ a i` on `Z/p` is `a^((p-1)/2)`), Euler's criterion,
and the corollary for the child frames of `Λ(μ, g)`. -/
namespace Uniform

theorem MEq.emod_eq {p : Nat} {a b : Int} (h : MEq p a b) : a % p = b % p :=
  Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd h)

theorem MEq.of_emod_eq {p : Nat} {a b : Int} (h : a % p = b % p) : MEq p a b :=
  Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.1 h)

theorem neg_one_pow_cases (k : Nat) : (-1 : Int) ^ k = 1 ∨ (-1 : Int) ^ k = -1 := by
  rw [neg_one_pow_eq]; split <;> simp

theorem unit_meq_iff {p : Nat} (hp : 3 ≤ p) {u v : Int} (hu : u = 1 ∨ u = -1)
    (hv : v = 1 ∨ v = -1) : MEq p u v ↔ u = v := by
  constructor
  · intro h
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · exact absurd h (MEq.not_one_neg_one hp)
    · exact absurd h.symm (MEq.not_one_neg_one hp)
    · rfl
  · intro h; exact MEq.of_eq h

theorem IsPrime.odd {p : Nat} (hp : IsPrime p) (hp2 : p ≠ 2) : p % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one p with h | h
  · rcases hp.2 2 (Nat.dvd_of_mod_eq_zero h) with h1 | h1 <;> omega
  · exact h

theorem IsPrime.three_le {p : Nat} (hp : IsPrime p) (hp2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le; omega

theorem int_not_dvd {p a : Nat} (ha : ¬ p ∣ a) : ¬ (p : Int) ∣ (a : Int) :=
  fun h => ha (Int.natCast_dvd_natCast.1 h)

/-- squares of units are `1` under the `(p-1)/2` power -/
theorem sq_pow_half {p x : Nat} (hp : IsPrime p) (hp2 : p ≠ 2) (hx : ¬ p ∣ x) :
    MEq p (((x : Int) * x) ^ ((p - 1) / 2)) 1 := by
  have hodd := hp.odd hp2
  have e : ((x : Int) * x) ^ ((p - 1) / 2) = (x : Int) ^ (p - 1) := by
    rw [Int.mul_pow, ← Int.pow_add]; congr 1; omega
  rw [e]; exact fermat hp hx

theorem fermat_pow_p {p a : Nat} (hp : IsPrime p) (ha : ¬ p ∣ a) :
    MEq p ((a : Int) ^ p) a := by
  have h2 := hp.two_le
  have e : (a : Int) ^ p = (a : Int) ^ (p - 1) * a := by
    rw [← Int.pow_succ]; congr 1; omega
  rw [e]
  have := (fermat hp ha).mul (MEq.refl (a : Int))
  rwa [Int.one_mul] at this

theorem pairs_length_odd {p : Nat} (hodd : p % 2 = 1) : (pairs p).length = p * ((p - 1) / 2) := by
  have hL := length_pairs p
  have hp : p = 2 * ((p - 1) / 2) + 1 := by omega
  generalize (p - 1) / 2 = h at hp ⊢
  generalize (pairs p).length = L at hL ⊢
  subst hp
  grind

/-- Sign of an affine bijection of `Z/p`: `sign(i ↦ m i + c) ≡ m^((p-1)/2)` (Vandermonde). -/
theorem affine_sign {p : Nat} (hp : IsPrime p) (hp2 : p ≠ 2) {σ : Nat → Nat}
    (hσ : IsPermOn p σ) {m : Nat} {c : Int} (hm : ¬ p ∣ m)
    (haff : ∀ i, i < p → MEq p (σ i) ((m : Int) * i + c)) :
    MEq p (permSign p σ) ((m : Int) ^ ((p - 1) / 2)) := by
  have hodd := hp.odd hp2
  have hV := vandermonde_perm (fun i : Nat => (i : Int)) hσ
  have hcong : MEq p (Vprod p (fun i : Nat => (i : Int)) σ)
      (((pairs p).map (fun q => (m : Int) * ((q.2 : Int) - (q.1 : Int)))).prod) := by
    unfold Vprod
    apply MEq.prod_map
    intro q hq
    rw [mem_pairs'] at hq
    have e1 := haff q.2 hq.2
    have e2 := haff q.1 (by omega)
    exact (e1.sub e2).trans (MEq.of_eq (by grind))
  rw [prod_map_mul_int, prod_map_const_int, pairs_length_odd hodd] at hcong
  have hVid : ((pairs p).map (fun q => ((q.2 : Nat) : Int) - ((q.1 : Nat) : Int))).prod
      = Vprod p (fun i : Nat => (i : Int)) (fun i => i) := rfl
  rw [hVid, hV] at hcong
  have hVnd : ¬ (p : Int) ∣ Vprod p (fun i : Nat => (i : Int)) (fun i => i) := by
    unfold Vprod
    apply not_dvd_prod_int hp
    intro y hy
    rcases List.mem_map.1 hy with ⟨q, hq, rfl⟩
    rw [mem_pairs'] at hq
    have e : ((q.2 : Nat) : Int) - ((q.1 : Nat) : Int) = ((q.2 - q.1 : Nat) : Int) := by omega
    simp only [e]
    exact int_not_dvd (IsPrime.not_dvd_of_pos_lt (by omega) (by omega))
  have h1 := hcong.cancel hp hVnd
  rw [Int.pow_mul] at h1
  exact h1.trans ((fermat_pow_p hp hm).pow _)

theorem affine_perm {p : Nat} (hp : IsPrime p) {σ : Nat → Nat} (hlt : ∀ i, i < p → σ i < p)
    {m : Nat} {c : Int} (hm : ¬ p ∣ m) (haff : ∀ i, i < p → MEq p (σ i) ((m : Int) * i + c)) :
    IsPermOn p σ := by
  refine ⟨hlt, fun i j hi hj h => ?_⟩
  have hj' : MEq p (σ i) ((m : Int) * j + c) := by rw [h]; exact haff j hj
  have h1 : MEq p ((m : Int) * i + c) ((m : Int) * j + c) := (haff i hi).symm.trans hj'
  have h2 : MEq p ((i : Int) * m) ((j : Int) * m) := by
    have := h1.sub (MEq.refl c)
    exact (MEq.of_eq (by grind)).trans (this.trans (MEq.of_eq (by grind)))
  have := (h2.cancel hp (int_not_dvd hm)).eq_of_lt (by omega) (by omega) (by omega) (by omega)
  omega

/-- **U3 (Zolotarev).** For an odd prime `p` and `p ∤ a`, the permutation `i ↦ a i` of `Z/p`
is a permutation whose sign is `a^((p-1)/2) mod p`. -/
theorem U3_zolotarev (p a : Nat) (hp : IsPrime p) (hp2 : p ≠ 2) (ha : ¬ p ∣ a) :
    IsPermOn p (mulMap p a) ∧
    permSign p (mulMap p a) % (p : Int) = ((a : Int) ^ ((p - 1) / 2)) % (p : Int) := by
  refine ⟨mulMap_perm hp ha, ?_⟩
  apply MEq.emod_eq
  apply affine_sign hp hp2 (mulMap_perm hp ha) ha (c := 0)
  intro i _
  simp only [mulMap, Int.natCast_emod, Int.natCast_mul, Int.add_zero]
  exact MEq.emod_self _

/-! ### Euler's criterion -/

/-- product over a duplicate-free list closed under a fixed-point-free involution `ι`
with `x ι(x) ≡ c` -/
theorem pairing_prod {p : Nat} (c : Int) (ι : Nat → Nat) :
    ∀ (n : Nat) (l : List Nat), l.length ≤ n → l.Nodup →
      (∀ x ∈ l, ι x ∈ l ∧ ι (ι x) = x ∧ ι x ≠ x ∧ MEq p ((x : Int) * (ι x : Int)) c) →
      l.length % 2 = 0 ∧
      MEq p ((l.map (fun x : Nat => (x : Int))).prod) (c ^ (l.length / 2)) := by
  intro n
  induction n with
  | zero =>
    intro l hl _ _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp; exact MEq.refl _
  | succ n ih =>
    intro l hl hnd hcl
    cases l with
    | nil => simp; exact MEq.refl _
    | cons x t =>
      rw [List.nodup_cons] at hnd
      obtain ⟨hιx, hιιx, hne, hxc⟩ := hcl x List.mem_cons_self
      have hιt : ι x ∈ t := by
        rcases List.mem_cons.1 hιx with h | h
        · exact absurd h hne
        · exact h
      have hperm : t.Perm (ι x :: t.erase (ι x)) := List.perm_cons_erase hιt
      have hlen' : (t.erase (ι x)).length = t.length - 1 := List.length_erase_of_mem hιt
      have hnd' : (t.erase (ι x)).Nodup := hnd.2.erase _
      have hcl' : ∀ y ∈ t.erase (ι x), ι y ∈ t.erase (ι x) ∧ ι (ι y) = y ∧ ι y ≠ y ∧
          MEq p ((y : Int) * (ι y : Int)) c := by
        intro y hy
        rw [hnd.2.mem_erase_iff] at hy
        obtain ⟨hy1, hy2⟩ := hy
        obtain ⟨hιy, hιιy, hney, hyc⟩ := hcl y (List.mem_cons_of_mem _ hy2)
        refine ⟨?_, hιιy, hney, hyc⟩
        rw [hnd.2.mem_erase_iff]
        refine ⟨fun h => ?_, ?_⟩
        · have : y = x := hιιy.symm.trans ((congrArg ι h).trans hιιx)
          exact hnd.1 (this ▸ hy2)
        · rcases List.mem_cons.1 hιy with h | h
          · exact absurd (hιιy.symm.trans (congrArg ι h)) hy1
          · exact h
      have htpos := List.length_pos_of_mem hιt
      have hlt : (t.erase (ι x)).length ≤ n := by simp at hl; omega
      obtain ⟨hev, hmeq⟩ := ih _ hlt hnd' hcl'
      refine ⟨by simp; omega, ?_⟩
      have hprod : ((x :: t).map (fun x : Nat => (x : Int))).prod
          = (x : Int) * (ι x : Int) * ((t.erase (ι x)).map (fun x : Nat => (x : Int))).prod := by
        simp only [List.map_cons, List.prod_cons]
        rw [perm_prod_int (hperm.map (fun x : Nat => (x : Int)))]
        simp only [List.map_cons, List.prod_cons]; grind
      rw [hprod]
      have hl2 : (x :: t).length / 2 = (t.erase (ι x)).length / 2 + 1 := by simp; omega
      rw [hl2, Int.pow_succ]
      exact (hxc.mul hmeq).trans (MEq.of_eq (Int.mul_comm _ _))

/-- inverse modulo `p` -/
def invMod (p x : Nat) : Nat := (x ^ (p - 2)) % p

theorem invMod_spec {p x : Nat} (hp : IsPrime p) (hx : ¬ p ∣ x) :
    MEq p ((x : Int) * (invMod p x : Int)) 1 ∧ invMod p x < p ∧ ¬ p ∣ invMod p x := by
  have h2 := hp.two_le
  have hm : MEq p ((x : Int) * (invMod p x : Int)) 1 := by
    have e1 : MEq p ((x : Int) * (invMod p x : Int)) ((x : Int) * (x : Int) ^ (p - 2)) := by
      apply (MEq.refl (x : Int)).mul
      simp only [invMod, Int.natCast_emod, Int.natCast_pow]
      exact MEq.emod_self _
    have e2 : (x : Int) * (x : Int) ^ (p - 2) = (x : Int) ^ (p - 1) := by
      rw [Int.mul_comm, ← Int.pow_succ]; congr 1; omega
    rw [e2] at e1
    exact e1.trans (fermat hp hx)
  refine ⟨hm, Nat.mod_lt _ (by omega), fun hd => ?_⟩
  have h0 : MEq p ((x : Int) * (invMod p x : Int)) 0 := by
    obtain ⟨k, hk⟩ := Int.natCast_dvd_natCast.2 hd
    exact ⟨x * k, by rw [hk]; grind⟩
  have := (hm.symm.trans h0)
  have h1 : (p : Int) ∣ 1 := by simpa [MEq] using this
  have := Int.eq_one_of_dvd_one (by omega) h1
  omega

theorem invMod_unique {p x y : Nat} (hp : IsPrime p) (hx : ¬ p ∣ x) (hy : y < p)
    (h : MEq p ((x : Int) * y) 1) : y = invMod p x := by
  obtain ⟨hm, hlt, _⟩ := invMod_spec hp hx
  have : MEq p ((y : Int) * x) ((invMod p x : Int) * x) :=
    (MEq.of_eq (Int.mul_comm _ _)).trans (h.trans (hm.symm.trans (MEq.of_eq (Int.mul_comm _ _))))
  have := (this.cancel hp (int_not_dvd hx)).eq_of_lt (by omega) (by omega) (by omega) (by omega)
  omega

theorem meq_pm_one_of_sq {p x : Nat} (hp : IsPrime p) (h : MEq p ((x : Int) * x) 1)
    (h1 : 2 ≤ x) (h2 : x + 2 ≤ p) : False := by
  have hd : (p : Int) ∣ ((x - 1 : Nat) : Int) * ((x + 1 : Nat) : Int) := by
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have e1 : ((x - 1 : Nat) : Int) = (x : Int) - 1 := by omega
    have e2 : ((x + 1 : Nat) : Int) = (x : Int) + 1 := by omega
    rw [e1, e2]; grind
  rcases hp.int_dvd_mul hd with h3 | h3
  · exact IsPrime.not_dvd_of_pos_lt (p := p) (by omega) (by omega) (Int.natCast_dvd_natCast.1 h3)
  · exact IsPrime.not_dvd_of_pos_lt (p := p) (by omega) (by omega) (Int.natCast_dvd_natCast.1 h3)

theorem meq_pred_neg_one {p : Nat} (h : 1 ≤ p) : MEq p ((p - 1 : Nat) : Int) (-1) :=
  ⟨1, by omega⟩

/-- Wilson's theorem. -/
theorem wilson {p : Nat} (hp : IsPrime p) (hp2 : p ≠ 2) :
    MEq p (((List.range' 1 (p - 1)).map (fun x : Nat => (x : Int))).prod) (-1) := by
  have h3 := hp.three_le hp2
  have hsplit : List.range' 1 (p - 1) = 1 :: (List.range' 2 (p - 3) ++ [p - 1]) := by
    rw [show p - 1 = (p - 3) + 1 + 1 by omega, List.range'_succ, List.range'_1_concat]
    simp; omega
  rw [hsplit]
  simp only [List.map_cons, List.map_append, List.prod_cons, List.prod_append_int, List.map_nil,
    List.prod_nil]
  let l := List.range' 2 (p - 3)
  have hl : ∀ x ∈ l, 2 ≤ x ∧ x + 2 ≤ p := by
    intro x hx; simp [l, List.mem_range'_1] at hx; omega
  have hcl : ∀ x ∈ l, invMod p x ∈ l ∧ invMod p (invMod p x) = x ∧ invMod p x ≠ x ∧
      MEq p ((x : Int) * (invMod p x : Int)) 1 := by
    intro x hx
    obtain ⟨hx2, hxp⟩ := hl x hx
    have hxd : ¬ p ∣ x := IsPrime.not_dvd_of_pos_lt (by omega) (by omega)
    obtain ⟨hm, hlt, hnd⟩ := invMod_spec hp hxd
    have h0 : invMod p x ≠ 0 := by intro h; rw [h] at hnd; exact hnd (Nat.dvd_zero p)
    have h1 : invMod p x ≠ 1 := by
      intro h; rw [h] at hm
      have := (hm.trans (MEq.of_eq (by simp) : MEq p 1 ((1 : Nat) : Int)))
      have := (MEq.of_eq (by simp) : MEq p ((x : Nat) : Int) ((x : Int) * ((1 : Nat) : Int))).trans this
      have := this.eq_of_lt (by omega) (by omega) (by omega) (by omega)
      omega
    have h4 : invMod p x ≠ p - 1 := by
      intro h; rw [h] at hm
      have hxm : MEq p (x : Int) ((p - 1 : Nat) : Int) := by
        obtain ⟨k, hk⟩ := hm
        refine ⟨x - k - 1, ?_⟩
        have e : ((p - 1 : Nat) : Int) = (p : Int) - 1 := by omega
        rw [e] at hk ⊢; grind
      have := hxm.eq_of_lt (by omega) (by omega) (by omega) (by omega)
      omega
    refine ⟨?_, ?_, ?_, hm⟩
    · simp [l, List.mem_range'_1]; omega
    · exact (invMod_unique hp hnd (by omega)
        ((MEq.of_eq (Int.mul_comm _ _)).trans hm)).symm
    · intro h; rw [h] at hm; exact meq_pm_one_of_sq hp hm hx2 hxp
  have hpair := pairing_prod (p := p) 1 (invMod p) l.length l (Nat.le_refl _) List.nodup_range' hcl
  rw [Int.one_pow] at hpair
  have := (MEq.refl (1 : Int)).mul (hpair.2.mul (meq_pred_neg_one (p := p) (by omega)))
  simpa using this

/-- Euler's criterion, the hard direction: a nonsquare unit has `g^((p-1)/2) ≡ -1`. -/
theorem euler_nonsquare {p g : Nat} (hp : IsPrime p) (hp2 : p ≠ 2) (hg : ¬ p ∣ g)
    (hns : ¬ IsSquareMod p g) : MEq p ((g : Int) ^ ((p - 1) / 2)) (-1) := by
  have h3 := hp.three_le hp2
  let ι : Nat → Nat := fun x => (g * invMod p x) % p
  have hprop : ∀ y, 1 ≤ y → y < p →
      ι y < p ∧ ¬ p ∣ ι y ∧ MEq p ((y : Int) * (ι y : Int)) g := by
    intro y hy1 hyp
    have hyd : ¬ p ∣ y := IsPrime.not_dvd_of_pos_lt (by omega) hyp
    obtain ⟨hm, _, hnd⟩ := invMod_spec hp hyd
    refine ⟨Nat.mod_lt _ (by omega), fun hd => ?_, ?_⟩
    · exact hp.not_dvd_mul hg hnd ((Nat.dvd_mod_iff (Nat.dvd_refl p)).1 hd)
    · have e1 : MEq p ((ι y : Nat) : Int) ((g : Int) * (invMod p y : Int)) := by
        simp only [ι, Int.natCast_emod, Int.natCast_mul]; exact MEq.emod_self _
      have := (MEq.refl (y : Int)).mul e1
      refine this.trans ?_
      have := (MEq.refl (g : Int)).mul hm
      exact (MEq.of_eq (by grind)).trans (this.trans (MEq.of_eq (by grind)))
  let l := List.range' 1 (p - 1)
  have hl : ∀ x ∈ l, 1 ≤ x ∧ x < p := by intro x hx; simp [l, List.mem_range'_1] at hx; omega
  have hcl : ∀ x ∈ l, ι x ∈ l ∧ ι (ι x) = x ∧ ι x ≠ x ∧ MEq p ((x : Int) * (ι x : Int)) g := by
    intro x hx
    obtain ⟨hx1, hxp⟩ := hl x hx
    obtain ⟨hlt, hnd, hm⟩ := hprop x hx1 hxp
    have hι1 : 1 ≤ ι x := by
      apply Nat.pos_of_ne_zero; intro h; rw [h] at hnd; exact hnd (Nat.dvd_zero p)
    refine ⟨?_, ?_, ?_, hm⟩
    · simp [l, List.mem_range'_1]; omega
    · obtain ⟨hlt2, _, hm2⟩ := hprop (ι x) hι1 hlt
      have : MEq p ((ι (ι x) : Int) * (ι x : Int)) ((x : Int) * (ι x : Int)) :=
        (MEq.of_eq (Int.mul_comm _ _)).trans (hm2.trans hm.symm)
      have := (this.cancel hp (int_not_dvd hnd)).eq_of_lt (by omega) (by omega) (by omega) (by omega)
      omega
    · intro h
      rw [h] at hm
      apply hns
      refine ⟨x, ?_⟩
      apply MEq.nat_mod
      simpa only [Int.natCast_mul] using hm
  have hpair := pairing_prod (p := p) (g : Int) ι l.length l (Nat.le_refl _) List.nodup_range' hcl
  have hlen : l.length = p - 1 := by simp [l]
  rw [hlen] at hpair
  exact hpair.2.symm.trans (wilson hp hp2)

/-- **U3, Euler's criterion.** -/
theorem U3_euler (p g : Nat) (hp : IsPrime p) (hp2 : p ≠ 2) (hg : ¬ p ∣ g) :
    ((g : Int) ^ ((p - 1) / 2)) % (p : Int) = (-1) % (p : Int) ↔ ¬ IsSquareMod p g := by
  constructor
  · intro h ⟨x, hx⟩
    have hxd : ¬ p ∣ x := by
      intro hd
      have : p ∣ x * x := Nat.dvd_trans hd (Nat.dvd_mul_right x x)
      have h0 : (x * x) % p = 0 := Nat.mod_eq_zero_of_dvd this
      rw [h0] at hx
      exact hg (Nat.dvd_of_mod_eq_zero hx.symm)
    have hsq : MEq p ((x : Int) * x) g := by
      have := MEq.of_nat_mod hx; simpa only [Int.natCast_mul] using this
    have h1 := (hsq.pow ((p - 1) / 2)).symm.trans (sq_pow_half hp hp2 hxd)
    exact MEq.not_one_neg_one (hp.three_le hp2) (h1.symm.trans (MEq.of_emod_eq h))
  · intro hns
    exact MEq.emod_eq (euler_nonsquare hp hp2 hg hns)

/-! ### The child frames of `Λ(μ, g)` -/

theorem lamPerm_affine (p mu g : Nat) (A : Nat → Bool) (hz : zA p A ≤ p) (i : Nat) :
    MEq p (lamPerm p mu g A i : Int)
      (((mu * g ^ suppCard p A : Nat) : Int) * i
        + ((mu * g ^ suppCard p A : Nat) : Int) * ((p : Int) - zA p A)) := by
  unfold lamPerm
  rw [Int.natCast_emod]
  refine (MEq.emod_self _).trans (MEq.of_eq ?_)
  rw [Int.natCast_mul (mu * g ^ suppCard p A) (i + p - zA p A)]
  have : ((i + p - zA p A : Nat) : Int) = (i : Int) + p - zA p A := by omega
  rw [this]; grind

theorem lamPerm_lt (p mu g : Nat) (hp : 0 < p) (A : Nat → Bool) (i : Nat) :
    lamPerm p mu g A i < p := Nat.mod_lt _ hp

theorem unit_mul_eq_one_iff {u v : Int} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) :
    u * v = 1 ↔ u = v := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> decide

/-- For nonempty proper `A` with `k = |A|`: `h_A` is a rotation iff `(g^((p-1)/2))^k ≡ (-1)^k`. -/
theorem lam_rotation_iff {p mu g : Nat} (hp : IsPrime p) (hp2 : p ≠ 2) (hmu0 : ¬ p ∣ mu)
    (hmu : IsSquareMod p mu) (hg0 : ¬ p ∣ g) (A : Nat → Bool) (hA : NonemptyProperOn p A) :
    IsRotation p (lamChild p mu g A) ↔
      MEq p (((g : Int) ^ ((p - 1) / 2)) ^ suppCard p A) ((-1) ^ suppCard p A) := by
  have h3 := hp.three_le hp2
  have hz := (U1_zA p hp A hA).1
  have hm : ¬ p ∣ mu * g ^ suppCard p A := hp.not_dvd_mul hmu0 (hp.not_dvd_pow hg0 _)
  have haff := fun i (_ : i < p) => lamPerm_affine p mu g A (by omega) i
  have hperm : IsPermOn p (lamPerm p mu g A) :=
    affine_perm hp (fun i _ => lamPerm_lt p mu g (by omega) A i) hm haff
  have hsign := affine_sign hp hp2 hperm hm haff
  -- `μ^h ≡ 1`
  obtain ⟨x, hx⟩ := hmu
  have hxd : ¬ p ∣ x := by
    intro hd
    have : p ∣ x * x := Nat.dvd_trans hd (Nat.dvd_mul_right x x)
    have h0 : (x * x) % p = 0 := Nat.mod_eq_zero_of_dvd this
    rw [h0] at hx
    exact hmu0 (Nat.dvd_of_mod_eq_zero hx.symm)
  have hsq : MEq p ((x : Int) * x) mu := by
    have := MEq.of_nat_mod hx; simpa only [Int.natCast_mul] using this
  have hmu1 : MEq p ((mu : Int) ^ ((p - 1) / 2)) 1 :=
    (hsq.pow _).symm.trans (sq_pow_half hp hp2 hxd)
  have e : (((mu * g ^ suppCard p A : Nat) : Int)) ^ ((p - 1) / 2)
      = (mu : Int) ^ ((p - 1) / 2) * ((g : Int) ^ ((p - 1) / 2)) ^ suppCard p A := by
    rw [Int.natCast_mul, Int.natCast_pow, Int.mul_pow, ← Int.pow_mul, ← Int.pow_mul,
      Nat.mul_comm]
  rw [e] at hsign
  have hsign' : MEq p (permSign p (lamPerm p mu g A))
      (((g : Int) ^ ((p - 1) / 2)) ^ suppCard p A) := by
    have := hsign.trans (hmu1.mul (MEq.refl (((g : Int) ^ ((p - 1) / 2)) ^ suppCard p A)))
    rwa [Int.one_mul] at this
  have hsp : signProd p A = (-1) ^ suppCard p A := signProd_eq p A
  have hu : permSign p (lamPerm p mu g A) = 1 ∨ permSign p (lamPerm p mu g A) = -1 :=
    neg_one_pow_cases _
  have hv := neg_one_pow_cases (suppCard p A)
  unfold IsRotation lamChild
  simp only
  rw [hsp, unit_mul_eq_one_iff hu hv, ← unit_meq_iff h3 hu hv]
  constructor
  · rintro ⟨_, h⟩; exact hsign'.symm.trans h
  · intro h; exact ⟨hperm, hsign'.trans h⟩

theorem suppCard_single (p : Nat) (hp : 0 < p) : suppCard p (fun i => decide (i = 0)) = 1 := by
  unfold suppCard
  rw [show p = (p - 1) + 1 by omega, List.range_succ_eq_map]
  simp [List.countP_map]

/-- **U3 corollary.** With `μ` a nonzero square, all child frames `h_A` of `Λ(μ, g)`
(nonempty proper `A`) are rotations iff `g` is a nonsquare mod `p`. -/
theorem U3_lambda_rotation (p mu g : Nat) (hp : IsPrime p) (hp2 : p ≠ 2)
    (hmu0 : ¬ p ∣ mu) (hmu : IsSquareMod p mu) (hg0 : ¬ p ∣ g) :
    (∀ A, NonemptyProperOn p A → IsRotation p (lamChild p mu g A)) ↔ ¬ IsSquareMod p g := by
  have h3 := hp.three_le hp2
  constructor
  · intro hall
    let A0 : Nat → Bool := fun i => decide (i = 0)
    have hA0 : NonemptyProperOn p A0 := ⟨⟨0, by omega, by simp [A0]⟩, ⟨1, by omega, by simp [A0]⟩⟩
    have h := (lam_rotation_iff hp hp2 hmu0 hmu hg0 A0 hA0).1 (hall A0 hA0)
    rw [suppCard_single p (by omega), Int.pow_one, Int.pow_one] at h
    exact (U3_euler p g hp hp2 hg0).1 (MEq.emod_eq h)
  · intro hns A hA
    rw [lam_rotation_iff hp hp2 hmu0 hmu hg0 A hA]
    exact (euler_nonsquare hp hp2 hg0 hns).pow _

end Uniform
