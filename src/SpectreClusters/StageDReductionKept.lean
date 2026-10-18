module

public import SpectreClusters.StageDReductionModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

def kept1 : ClusterKind → List Nat
  | .t7h => [127,134,136,139,140,143]
  | .t8h => [727,729,753,759,1237,1253,1267,1269,1275,1277,1289,1325,1331,1627,1628,1629,1651,1652,1653,1716,1717,1732,1733,1747,1748,1749,1755,1756,1757]
  | .t6h => []

def kept2 : ClusterKind → List Nat
  | .t7h => [139,140]
  | .t8h => [727,729,753,759,1237,1253,1267,1275,1289,1627,1628,1651,1652,1716,1732,1747,1748,1755,1756]
  | .t6h => []

def kept3 : ClusterKind → List Nat
  | .t7h => [139,140]
  | .t8h => [727,729,753,759,1237,1253,1267,1275,1627,1628,1651,1652,1716,1732,1747,1748,1755,1756]
  | .t6h => []

def kept (s : Nat) (k : ClusterKind) : List Nat :=
  match s with
  | 0 => List.range (compactRowIDs k).length
  | 1 => kept1 k
  | 2 => kept2 k
  | _ => kept3 k
end SpectreClusters.StageD.Reduction
