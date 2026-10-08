module
public import SparseMonotiles.T7FullCrossMate
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7FullForward
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact original parents160–191; all128 roots and every generated role. -/
theorem cross_checks_group5 (k : Fin 408) (hl : 160 ≤ k.val) (hu : k.val < 192)
    (a : Fin 128) : sparseMemberChecks 7 registryFields (childFields a) (crossFields k)
      (crossRows crossMate k a) = true := by
  by_cases h160 : k.val = 160
  · have hk : k = 160 := Fin.ext h160
    subst k
    exact T7AggregateParent160.all_checked a
  by_cases h161 : k.val = 161
  · have hk : k = 161 := Fin.ext h161
    subst k
    exact T7AggregateParent161.all_checked a
  by_cases h162 : k.val = 162
  · have hk : k = 162 := Fin.ext h162
    subst k
    exact T7AggregateParent162.all_checked a
  by_cases h163 : k.val = 163
  · have hk : k = 163 := Fin.ext h163
    subst k
    exact T7AggregateParent163.all_checked a
  by_cases h164 : k.val = 164
  · have hk : k = 164 := Fin.ext h164
    subst k
    exact T7AggregateParent164.all_checked a
  by_cases h165 : k.val = 165
  · have hk : k = 165 := Fin.ext h165
    subst k
    exact T7AggregateParent165.all_checked a
  by_cases h166 : k.val = 166
  · have hk : k = 166 := Fin.ext h166
    subst k
    exact T7AggregateParent166.all_checked a
  by_cases h167 : k.val = 167
  · have hk : k = 167 := Fin.ext h167
    subst k
    exact T7AggregateParent167.all_checked a
  by_cases h168 : k.val = 168
  · have hk : k = 168 := Fin.ext h168
    subst k
    exact T7AggregateParent168.all_checked a
  by_cases h169 : k.val = 169
  · have hk : k = 169 := Fin.ext h169
    subst k
    exact T7AggregateParent169.all_checked a
  by_cases h170 : k.val = 170
  · have hk : k = 170 := Fin.ext h170
    subst k
    exact T7AggregateParent170.all_checked a
  by_cases h171 : k.val = 171
  · have hk : k = 171 := Fin.ext h171
    subst k
    exact T7AggregateParent171.all_checked a
  by_cases h172 : k.val = 172
  · have hk : k = 172 := Fin.ext h172
    subst k
    exact T7AggregateParent172.all_checked a
  by_cases h173 : k.val = 173
  · have hk : k = 173 := Fin.ext h173
    subst k
    exact T7AggregateParent173.all_checked a
  by_cases h174 : k.val = 174
  · have hk : k = 174 := Fin.ext h174
    subst k
    exact T7AggregateParent174.all_checked a
  by_cases h175 : k.val = 175
  · have hk : k = 175 := Fin.ext h175
    subst k
    exact T7AggregateParent175.all_checked a
  by_cases h176 : k.val = 176
  · have hk : k = 176 := Fin.ext h176
    subst k
    exact T7AggregateParent176.all_checked a
  by_cases h177 : k.val = 177
  · have hk : k = 177 := Fin.ext h177
    subst k
    exact T7AggregateParent177.all_checked a
  by_cases h178 : k.val = 178
  · have hk : k = 178 := Fin.ext h178
    subst k
    exact T7AggregateParent178.all_checked a
  by_cases h179 : k.val = 179
  · have hk : k = 179 := Fin.ext h179
    subst k
    exact T7AggregateParent179.all_checked a
  by_cases h180 : k.val = 180
  · have hk : k = 180 := Fin.ext h180
    subst k
    exact T7AggregateParent180.all_checked a
  by_cases h181 : k.val = 181
  · have hk : k = 181 := Fin.ext h181
    subst k
    exact T7AggregateParent181.all_checked a
  by_cases h182 : k.val = 182
  · have hk : k = 182 := Fin.ext h182
    subst k
    exact T7AggregateParent182.all_checked a
  by_cases h183 : k.val = 183
  · have hk : k = 183 := Fin.ext h183
    subst k
    exact T7AggregateParent183.all_checked a
  by_cases h184 : k.val = 184
  · have hk : k = 184 := Fin.ext h184
    subst k
    exact T7AggregateParent184.all_checked a
  by_cases h185 : k.val = 185
  · have hk : k = 185 := Fin.ext h185
    subst k
    exact T7AggregateParent185.all_checked a
  by_cases h186 : k.val = 186
  · have hk : k = 186 := Fin.ext h186
    subst k
    exact T7AggregateParent186.all_checked a
  by_cases h187 : k.val = 187
  · have hk : k = 187 := Fin.ext h187
    subst k
    exact T7AggregateParent187.all_checked a
  by_cases h188 : k.val = 188
  · have hk : k = 188 := Fin.ext h188
    subst k
    exact T7AggregateParent188.all_checked a
  by_cases h189 : k.val = 189
  · have hk : k = 189 := Fin.ext h189
    subst k
    exact T7AggregateParent189.all_checked a
  by_cases h190 : k.val = 190
  · have hk : k = 190 := Fin.ext h190
    subst k
    exact T7AggregateParent190.all_checked a
  have hk : k = 191 := Fin.ext (by omega)
  subst k
  exact T7AggregateParent191.all_checked a

#print axioms cross_checks_group5
end SparseMonotiles.CarrierHierarchy.T7FullForward
