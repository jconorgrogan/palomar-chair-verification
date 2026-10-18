module

public import SpectreFinite.HexWordQuotient

@[expose] public section


/-! Explicit finite exhaustion of direction words. -/
namespace SpectreFinite.HexSearch

def wordBall : Nat → List HexWord
  | 0 => [[]]
  | n+1 => [] :: (List.finRange 6).flatMap (fun d => (wordBall n).map (d :: ·))

theorem mem_wordBall_iff (n : Nat) (w : HexWord) : w ∈ wordBall n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => cases w <;> simp [wordBall]
  | succ n ih =>
    cases w with
    | nil => simp [wordBall]
    | cons d w => simp [wordBall,List.mem_flatMap,List.mem_map,ih]

theorem wordBall_nodup (n : Nat) : (wordBall n).Nodup := by
  induction n with
  | zero => simp [wordBall]
  | succ n ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,?_⟩
    · simp [List.mem_flatMap,List.mem_map]
    · apply List.pairwise_flatMap.mpr
      constructor
      · intro d hd
        exact List.Pairwise.map _ (fun x y h he => h (List.cons.inj he).2) ih
      · apply List.Pairwise.imp _ (List.nodup_finRange 6)
        intro d e hde x hx y hy he
        obtain ⟨u,hu,hux⟩ := List.mem_map.mp hx
        obtain ⟨v,hv,hvy⟩ := List.mem_map.mp hy
        exact hde (List.cons.inj (hux.trans (he.trans hvy.symm))).1

theorem wordBall_mono {n m : Nat} (h : n ≤ m) : wordBall n ⊆ wordBall m := by
  intro w hw
  exact (mem_wordBall_iff m w).mpr (Nat.le_trans ((mem_wordBall_iff n w).mp hw) h)

end SpectreFinite.HexSearch
