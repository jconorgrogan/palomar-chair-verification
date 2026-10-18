module

public import SparseMonotiles.GeneratorPairFast5
public import SparseMonotiles.GeneratorRowCoverageFast

@[expose] public section

namespace SparseMonotiles.Contact.IndexedData5

/-- Same checked fields, using named constant-size lookup subtrees. -/
noncomputable def generatorNamedPairCertificateB {ρ : Type*} (lookup : ρ → Pose 5)
    (a b : Fin 256) : GeneratorPairCertificate 5 ρ → Bool
  | .absent => decide (generatorFastPair a b = none)
  | .row address => pairFieldsMatchB geometry.denominator
      (fastFacet (generatorFastOwner a)) (fastFacet (generatorFastOwner b))
      (generatorFastKey a) (generatorFastKey b) (lookup address)
  | .overlap root source => decide
      (GeneratorPairCertificate.ChairValid lookup (generatorFastPair a b)
        (.overlap root source))

theorem generatorNamedPairCertificateB_sound {ρ : Type*} (lookup : ρ → Pose 5)
    {a b : Fin 256} {cert : GeneratorPairCertificate 5 ρ}
    (h : generatorNamedPairCertificateB lookup a b cert = true) :
    cert.ChairValid lookup (generatorIndexing.pair a b) := by
  cases cert with
  | absent =>
      have he : generatorFastPair a b = none := of_decide_eq_true h
      change generatorIndexing.pair a b = none
      simpa only [generatorFastPair_eq] using he
  | overlap root source =>
      have he : (GeneratorPairCertificate.overlap root source :
          GeneratorPairCertificate 5 ρ).ChairValid lookup (generatorFastPair a b) :=
        of_decide_eq_true h
      simpa only [generatorFastPair_eq] using he
  | row address =>
      have he : generatorFastPair a b = some (lookup address) :=
        pairFieldsMatchB_sound (by decide) h
      rw [generatorFastPair_eq] at he
      change optionPoseMatches (generatorIndexing.pair a b) (lookup address)
      rw [he]
      intro i
      exact ⟨rfl, rfl, rfl⟩

#print axioms generatorNamedPairCertificateB_sound
end SparseMonotiles.Contact.IndexedData5
