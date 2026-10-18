module

public import SpectreFinite.LargerWindowPruning

@[expose] public section


/-! A checked optimization of the same finite certificates. Coordinate
signatures may be computed from indexed state rows after a uniform theorem
has related both signature computations for every row, including short rows.
This changes neither the coverage invariant nor the occurrence argument. -/
namespace SpectreFinite.HexSearch.LargerWindowPruning

open SignaturePruning (KeyTree accepts)

def indexSignature (indices : List Nat) (row : List State) : Nat :=
  encode (indices.map (fun i => (row[i]?).getD (0,0)))

inductive RowVerdict (n : Nat) where
  | keep (row : List State)
  | reject (row : List State) (direction : Fin n)

def RowVerdict.row : RowVerdict n → List State
  | .keep row => row
  | .reject row _ => row

def materialize (domain : List Position) : RowVerdict n → Verdict n
  | .keep row => .keep (domain.zip row)
  | .reject row d => .reject (domain.zip row) d

def checkIndexedCoverage (indices : Fin n → List Nat) (trees : Fin n → KeyTree)
    (v : RowVerdict n) : Bool :=
  (List.finRange n).all (fun d => accepts (trees d) (indexSignature (indices d) v.row))

def checkIndexedVerdict (indices : Fin n → List Nat) (trees : Fin n → KeyTree) :
    RowVerdict n → Bool
  | .keep _ => true
  | .reject row d => !(accepts (trees d) (indexSignature (indices d) row))

def checkIndexedRows (left right : Fin n → List Nat) (trees : Fin n → KeyTree)
    (rows : List (RowVerdict n)) : Bool :=
  rows.all (fun v => checkIndexedCoverage right trees v && checkIndexedVerdict left trees v)

theorem checkCoverage_materialize (domain : List Position)
    (samples : Fin n → List Position) (right : Fin n → List Nat)
    (hright : ∀ d row, rightSignature (samples d) (domain.zip row) =
      indexSignature (right d) row)
    (trees : Fin n → KeyTree) (v : RowVerdict n) :
    checkCoverage samples trees (materialize domain v) = checkIndexedCoverage right trees v := by
  cases v with
  | keep row =>
      unfold checkCoverage checkIndexedCoverage
      congr 1
      funext d
      exact congrArg (accepts (trees d)) (hright d row)
  | reject row direction =>
      unfold checkCoverage checkIndexedCoverage
      congr 1
      funext d
      exact congrArg (accepts (trees d)) (hright d row)

theorem checkVerdict_materialize (domain : List Position) (offsets : Fin n → Position)
    (samples : Fin n → List Position) (left : Fin n → List Nat)
    (hleft : ∀ d row, leftSignature (offsets d) (samples d) (domain.zip row) =
      indexSignature (left d) row)
    (trees : Fin n → KeyTree) (v : RowVerdict n) :
    checkVerdict offsets samples trees (materialize domain v) = checkIndexedVerdict left trees v := by
  cases v with
  | keep row => rfl
  | reject row d =>
      change (!(accepts (trees d) (leftSignature (offsets d) (samples d) (domain.zip row)))) =
        (!(accepts (trees d) (indexSignature (left d) row)))
      rw [hleft]

theorem checkRows_materialize (domain : List Position) (offsets : Fin n → Position)
    (samples : Fin n → List Position) (left right : Fin n → List Nat)
    (hleft : ∀ d row, leftSignature (offsets d) (samples d) (domain.zip row) =
      indexSignature (left d) row)
    (hright : ∀ d row, rightSignature (samples d) (domain.zip row) =
      indexSignature (right d) row)
    (trees : Fin n → KeyTree) (rows : List (RowVerdict n)) :
    checkRows offsets samples trees (rows.map (materialize domain)) =
      checkIndexedRows left right trees rows := by
  simp only [checkRows, checkIndexedRows, List.all_map]
  congr 1
  funext v
  change (checkCoverage samples trees (materialize domain v) &&
    checkVerdict offsets samples trees (materialize domain v)) = _
  rw [checkCoverage_materialize domain samples right hright,
    checkVerdict_materialize domain offsets samples left hleft]

#print axioms checkRows_materialize
end SpectreFinite.HexSearch.LargerWindowPruning
