module

public import SpectreFinite.SignaturePruning

@[expose] public section


namespace SpectreFinite.HexSearch.SignaturePruning

theorem checkRows_flatten (trees : Fin 6 → KeyTree) (chunks : List (List Verdict))
    (h : chunks.all (fun rows => checkRows trees rows) = true) :
    checkRows trees chunks.flatten = true := by
  induction chunks with
  | nil => rfl
  | cons a as ih =>
      have ha := (Bool.and_eq_true_iff.mp h).1
      have has := (Bool.and_eq_true_iff.mp h).2
      exact checkRows_append trees a as.flatten ha (ih has)

end SpectreFinite.HexSearch.SignaturePruning
