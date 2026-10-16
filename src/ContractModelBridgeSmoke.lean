/- SPDX-License-Identifier: Apache-2.0
Diagnostic only. Does not prove either Challenge theorem. -/
module
public import PalomarCurvedChallenge
public import PalomarKeyedProductChallenge
public import SparseMonotiles.Model
public section

theorem curved_model_eq (T : Set PalomarCurved.Plane) :
    (IsCompact T ∧ PalomarCurved.HasTiling T ∧ PalomarCurved.IsAperiodic T) =
      SparseMonotiles.IsAperiodicMonotile T := rfl

theorem keyed_product_model_eq (T : Set PalomarKeyedProduct.Four) :
    (IsCompact T ∧ PalomarKeyedProduct.HasTiling T ∧ PalomarKeyedProduct.IsAperiodic T) =
      SparseMonotiles.IsAperiodicMonotile T := rfl

#print axioms curved_model_eq
#print axioms keyed_product_model_eq
