module

public import SpectreGeometry.PolygonData

@[expose] public section


/-! Exact separation certificates for the optimized product-key centers.

The polygon data stores twice each vertex. The integer-quadratic numerator
below therefore stores eight times each active center, with false = 1/4 and
true = 3/4 along its edge. No floating-point calculation is used. The only
finite checks are 28-by-28 planar separation and 28 distances from (4,4).
The real consumer separately proves the scaling and the 56-center result. -/
namespace SpectreGeometry

/-- Integer scaling, without introducing real or rational dependencies. -/
def productKeyExactScale (n : Int) (x : ExactPoint) : ExactPoint :=
  (Quad3.mul (n,0) x.1, Quad3.mul (n,0) x.2)

/-- Eight times the active center, in the integer-pair model of Q(√3). -/
def productKeyCenterNumerator (i : Fin 14) (e : Bool) : ExactPoint :=
  ExactPoint.add (productKeyExactScale 4 (vertex i))
    (productKeyExactScale (if e then 3 else 1) (edge i))

def productKeyNumeratorDistanceSquared (i j : Fin 14) (e f : Bool) : Quad3 :=
  let d := ExactPoint.sub (productKeyCenterNumerator i e) (productKeyCenterNumerator j f)
  ExactPoint.dot d d

def productKeyPassiveNumeratorDistanceSquared (i : Fin 14) (e : Bool) : Quad3 :=
  let d := ExactPoint.sub (productKeyCenterNumerator i e) ((4,0),(4,0))
  ExactPoint.dot d d

/-- An exact nonnegative certificate, allowing the attained minimum. -/
def productKeyQuadNonnegative (q : Quad3) : Prop := q = (0,0) ∨ Quad3.positive q
instance (q : Quad3) : Decidable (productKeyQuadNonnegative q) :=
  inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- All 28 active centers: scaled squared separation is at least eight. -/
theorem product_key_numerator_separation : ∀ (i j : Fin 14) (e f : Bool),
    (i,e) ≠ (j,f) →
    productKeyQuadNonnegative (Quad3.sub (productKeyNumeratorDistanceSquared i j e f) (8,0)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- All active centers are at scaled squared distance at least twenty from
(4,4), the numerator of the passive anchor (1/2,1/2). -/
theorem product_key_passive_numerator_separation : ∀ (i : Fin 14) (e : Bool),
    productKeyQuadNonnegative (Quad3.sub (productKeyPassiveNumeratorDistanceSquared i e) (20,0)) := by
  decide

end SpectreGeometry
