module

public import Init

@[expose] public section


/-! Original exact integer halfplane/BSP proof certificates. A facet (a,b,c)
means a*x+b*y+c >= 0. Sparse weights are (hypothesis index, natural weight).
All checking is kernel-reducible integer arithmetic; real soundness is separate. -/
namespace SpectreGeometry.HalfplaneCertificate

abbrev Constraint := Int × Int × Int
abbrev SparseWeights := List (Nat × Nat)
def zeroConstraint : Constraint := (0,0,0)
def addConstraint (a b : Constraint) : Constraint := (a.1+b.1,a.2.1+b.2.1,a.2.2+b.2.2)
def negConstraint (a : Constraint) : Constraint := (-a.1,-a.2.1,-a.2.2)
def scaleConstraint (n : Nat) (a : Constraint) : Constraint :=
  ((n : Int)*a.1,(n : Int)*a.2.1,(n : Int)*a.2.2)
def lookupConstraint : List Constraint → Nat → Constraint
  | [],_ => zeroConstraint
  | a::_,0 => a
  | _::as,n+1 => lookupConstraint as n

def combine (hypotheses : List Constraint) : SparseWeights → Constraint
  | [] => zeroConstraint
  | (i,w)::ws => addConstraint (scaleConstraint w (lookupConstraint hypotheses i)) (combine hypotheses ws)

structure FacetWitness where
  scale : Nat
  weights : SparseWeights
  deriving Inhabited

def checkFacet (hypotheses : List Constraint) (goal : Constraint) (w : FacetWitness) : Bool :=
  decide (0 < w.scale) && decide (combine hypotheses w.weights = scaleConstraint w.scale goal)

def checkFacets (hypotheses : List Constraint) : List Constraint → List FacetWitness → Bool
  | [],_ => true
  | goal::goals,w::ws => checkFacet hypotheses goal w && checkFacets hypotheses goals ws
  | _::_,[] => false

inductive CoverTree where
  | leaf (target : Nat) (witnesses : List FacetWitness)
  | split (line : Constraint) (nonnegative nonpositive : CoverTree)
  | empty (weights : SparseWeights)

def checkTree (hypotheses : List Constraint) (targets : List (List Constraint)) : CoverTree → Bool
  | .leaf target witnesses => decide (target < targets.length) &&
      checkFacets hypotheses (targets.getD target []) witnesses
  | .split line pos neg => checkTree (hypotheses++[line]) targets pos &&
      checkTree (hypotheses++[negConstraint line]) targets neg
  | .empty weights => decide (combine hypotheses weights = (0,0,-1))

end SpectreGeometry.HalfplaneCertificate
