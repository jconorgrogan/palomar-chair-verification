module

public import SpectreClusters.ReverseClusterCocycleData

@[expose] public section


/-! A seven-vector envelope, and exact positive Gram certificates for all
49 independent adjacent-direction pairs. No embedding is asserted here. -/
namespace SpectreClusters.ReverseExistence
open SpectreFinite SpectreFinite.HexSearch

def westDeltas : List Point :=
  [(-18,6),(-16,2),(-14,4),(-12,0),(-12,6),(-10,2),(-8,-2)]
def deltaOptions (d : Fin 6) : List Point := westDeltas.map (rotate d)

def DeltaBoundCertificate (k : Fin 9) : Prop :=
  ∀ (r : Fin 6) (j : Fin 9) (t : Fin 6) (d : Fin 6), sideMatch (k,r) (j,t) d →
    vertexDelta (k,r) (j,t) d ∈ deltaOptions d

/-- Row-major residual numerator for J=[-u,-v], with u a west delta and
v a south delta. The actual residual is this integer matrix divided by16. -/
def anchorResidual (i j : Fin 7) : Int × Int × Int × Int :=
  let u := westDeltas.getD i.val (0,0)
  let v := rotate 1 (westDeltas.getD j.val (0,0))
  (16+u.1,v.1,u.2,16+v.2)

/-- Twice the triangular metric Gram matrix is [[2,1],[1,2]]. This gives
225G−RᵀGR; positivity proves ||I−J/16||_G <15/16. -/
def anchorGramGap (i j : Fin 7) : Int × Int × Int :=
  let r := anchorResidual i j
  let a := r.1; let b := r.2.1; let c := r.2.2.1; let d := r.2.2.2
  (450-(2*a*a+2*a*c+2*c*c),225-(2*a*b+a*d+c*b+2*c*d),
    450-(2*b*b+2*b*d+2*d*d))

def AnchorMatrixCertificate (i j : Fin 7) : Prop :=
  let q := anchorGramGap i j
  0 < q.1 ∧ 0 < q.1*q.2.2-q.2.1*q.2.1
instance (i j : Fin 7) : Decidable (AnchorMatrixCertificate i j) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem anchor_matrix_certificate : ∀ i j : Fin 7, AnchorMatrixCertificate i j := by decide

end SpectreClusters.ReverseExistence
