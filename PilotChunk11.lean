module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose352 : Pose 7 := ⟨perm0, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row352_fields : pairFieldsMatchB 188160 facet0 facet308 key0 key352 rowPose352 = true := by decide +kernel
theorem row352_generated : rootPair 352 = some rowPose352 :=
  pairFieldsMatchB_sound (by decide) row352_fields
theorem row352_source : sourceKey 352 ∈ geometry.profile (sourceOwner 352) := by decide +kernel
theorem row352_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 308 key0).FastValid geometry rowPose352 := by decide +kernel
theorem row352_illegal : ¬ geometry.LegalContact rowPose352 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row352_reject_checked)
theorem row352_classified : RowClassified 352 := by
  intro p generated legal
  have he : rowPose352 = p := Option.some.inj (row352_generated.symm.trans generated)
  subst p
  exact (row352_illegal legal).elim

def rowPose353 : Pose 7 := ⟨perm16, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row353_fields : pairFieldsMatchB 188160 facet0 facet309 key0 key353 rowPose353 = true := by decide +kernel
theorem row353_generated : rootPair 353 = some rowPose353 :=
  pairFieldsMatchB_sound (by decide) row353_fields
theorem row353_source : sourceKey 353 ∈ geometry.profile (sourceOwner 353) := by decide +kernel
theorem row353_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 309 key1).FastValid geometry rowPose353 := by decide +kernel
theorem row353_illegal : ¬ geometry.LegalContact rowPose353 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row353_reject_checked)
theorem row353_classified : RowClassified 353 := by
  intro p generated legal
  have he : rowPose353 = p := Option.some.inj (row353_generated.symm.trans generated)
  subst p
  exact (row353_illegal legal).elim

def rowPose354 : Pose 7 := ⟨perm40, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row354_fields : pairFieldsMatchB 188160 facet0 facet310 key0 key354 rowPose354 = true := by decide +kernel
theorem row354_generated : rootPair 354 = some rowPose354 :=
  pairFieldsMatchB_sound (by decide) row354_fields
theorem row354_source : sourceKey 354 ∈ geometry.profile (sourceOwner 354) := by decide +kernel
theorem row354_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 310 key0).FastValid geometry rowPose354 := by decide +kernel
theorem row354_illegal : ¬ geometry.LegalContact rowPose354 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row354_reject_checked)
theorem row354_classified : RowClassified 354 := by
  intro p generated legal
  have he : rowPose354 = p := Option.some.inj (row354_generated.symm.trans generated)
  subst p
  exact (row354_illegal legal).elim

def rowPose355 : Pose 7 := ⟨perm53, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row355_fields : pairFieldsMatchB 188160 facet0 facet311 key0 key355 rowPose355 = true := by decide +kernel
theorem row355_generated : rootPair 355 = some rowPose355 :=
  pairFieldsMatchB_sound (by decide) row355_fields
theorem row355_source : sourceKey 355 ∈ geometry.profile (sourceOwner 355) := by decide +kernel
theorem row355_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 311 key1).FastValid geometry rowPose355 := by decide +kernel
theorem row355_illegal : ¬ geometry.LegalContact rowPose355 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row355_reject_checked)
theorem row355_classified : RowClassified 355 := by
  intro p generated legal
  have he : rowPose355 = p := Option.some.inj (row355_generated.symm.trans generated)
  subst p
  exact (row355_illegal legal).elim

def rowPose356 : Pose 7 := ⟨perm74, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row356_fields : pairFieldsMatchB 188160 facet0 facet312 key0 key356 rowPose356 = true := by decide +kernel
theorem row356_generated : rootPair 356 = some rowPose356 :=
  pairFieldsMatchB_sound (by decide) row356_fields
theorem row356_source : sourceKey 356 ∈ geometry.profile (sourceOwner 356) := by decide +kernel
theorem row356_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 312 key1).FastValid geometry rowPose356 := by decide +kernel
theorem row356_illegal : ¬ geometry.LegalContact rowPose356 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row356_reject_checked)
theorem row356_classified : RowClassified 356 := by
  intro p generated legal
  have he : rowPose356 = p := Option.some.inj (row356_generated.symm.trans generated)
  subst p
  exact (row356_illegal legal).elim

def rowPose357 : Pose 7 := ⟨perm90, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row357_fields : pairFieldsMatchB 188160 facet0 facet313 key0 key357 rowPose357 = true := by decide +kernel
theorem row357_generated : rootPair 357 = some rowPose357 :=
  pairFieldsMatchB_sound (by decide) row357_fields
theorem row357_source : sourceKey 357 ∈ geometry.profile (sourceOwner 357) := by decide +kernel
theorem row357_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 285 key8).FastValid geometry rowPose357 := by decide +kernel
theorem row357_illegal : ¬ geometry.LegalContact rowPose357 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row357_reject_checked)
theorem row357_classified : RowClassified 357 := by
  intro p generated legal
  have he : rowPose357 = p := Option.some.inj (row357_generated.symm.trans generated)
  subst p
  exact (row357_illegal legal).elim

def rowPose358 : Pose 7 := ⟨perm87, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row358_fields : pairFieldsMatchB 188160 facet0 facet313 key0 key358 rowPose358 = true := by decide +kernel
theorem row358_generated : rootPair 358 = some rowPose358 :=
  pairFieldsMatchB_sound (by decide) row358_fields
theorem row358_source : sourceKey 358 ∈ geometry.profile (sourceOwner 358) := by decide +kernel
theorem row358_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 313 key0).FastValid geometry rowPose358 := by decide +kernel
theorem row358_illegal : ¬ geometry.LegalContact rowPose358 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row358_reject_checked)
theorem row358_classified : RowClassified 358 := by
  intro p generated legal
  have he : rowPose358 = p := Option.some.inj (row358_generated.symm.trans generated)
  subst p
  exact (row358_illegal legal).elim

def rowPose359 : Pose 7 := ⟨perm111, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row359_fields : pairFieldsMatchB 188160 facet0 facet314 key0 key359 rowPose359 = true := by decide +kernel
theorem row359_generated : rootPair 359 = some rowPose359 :=
  pairFieldsMatchB_sound (by decide) row359_fields
theorem row359_source : sourceKey 359 ∈ geometry.profile (sourceOwner 359) := by decide +kernel
theorem row359_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 314 key0).FastValid geometry rowPose359 := by decide +kernel
theorem row359_illegal : ¬ geometry.LegalContact rowPose359 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row359_reject_checked)
theorem row359_classified : RowClassified 359 := by
  intro p generated legal
  have he : rowPose359 = p := Option.some.inj (row359_generated.symm.trans generated)
  subst p
  exact (row359_illegal legal).elim

def rowPose360 : Pose 7 := ⟨perm0, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row360_fields : pairFieldsMatchB 188160 facet0 facet315 key0 key360 rowPose360 = true := by decide +kernel
theorem row360_generated : rootPair 360 = some rowPose360 :=
  pairFieldsMatchB_sound (by decide) row360_fields
theorem row360_source : sourceKey 360 ∈ geometry.profile (sourceOwner 360) := by decide +kernel
theorem row360_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 315 key0).FastValid geometry rowPose360 := by decide +kernel
theorem row360_illegal : ¬ geometry.LegalContact rowPose360 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row360_reject_checked)
theorem row360_classified : RowClassified 360 := by
  intro p generated legal
  have he : rowPose360 = p := Option.some.inj (row360_generated.symm.trans generated)
  subst p
  exact (row360_illegal legal).elim

def rowPose361 : Pose 7 := ⟨perm15, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row361_fields : pairFieldsMatchB 188160 facet0 facet315 key0 key361 rowPose361 = true := by decide +kernel
theorem row361_generated : rootPair 361 = some rowPose361 :=
  pairFieldsMatchB_sound (by decide) row361_fields
theorem row361_source : sourceKey 361 ∈ geometry.profile (sourceOwner 361) := by decide +kernel
theorem row361_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 91 key8).FastValid geometry rowPose361 := by decide +kernel
theorem row361_illegal : ¬ geometry.LegalContact rowPose361 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row361_reject_checked)
theorem row361_classified : RowClassified 361 := by
  intro p generated legal
  have he : rowPose361 = p := Option.some.inj (row361_generated.symm.trans generated)
  subst p
  exact (row361_illegal legal).elim

def rowPose362 : Pose 7 := ⟨perm21, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row362_fields : pairFieldsMatchB 188160 facet0 facet316 key0 key362 rowPose362 = true := by decide +kernel
theorem row362_generated : rootPair 362 = some rowPose362 :=
  pairFieldsMatchB_sound (by decide) row362_fields
theorem row362_source : sourceKey 362 ∈ geometry.profile (sourceOwner 362) := by decide +kernel
theorem row362_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 316 key1).FastValid geometry rowPose362 := by decide +kernel
theorem row362_illegal : ¬ geometry.LegalContact rowPose362 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row362_reject_checked)
theorem row362_classified : RowClassified 362 := by
  intro p generated legal
  have he : rowPose362 = p := Option.some.inj (row362_generated.symm.trans generated)
  subst p
  exact (row362_illegal legal).elim

def rowPose363 : Pose 7 := ⟨perm42, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row363_fields : pairFieldsMatchB 188160 facet0 facet317 key0 key363 rowPose363 = true := by decide +kernel
theorem row363_generated : rootPair 363 = some rowPose363 :=
  pairFieldsMatchB_sound (by decide) row363_fields
theorem row363_source : sourceKey 363 ∈ geometry.profile (sourceOwner 363) := by decide +kernel
theorem row363_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 317 key1).FastValid geometry rowPose363 := by decide +kernel
theorem row363_illegal : ¬ geometry.LegalContact rowPose363 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row363_reject_checked)
theorem row363_classified : RowClassified 363 := by
  intro p generated legal
  have he : rowPose363 = p := Option.some.inj (row363_generated.symm.trans generated)
  subst p
  exact (row363_illegal legal).elim

def rowPose364 : Pose 7 := ⟨perm55, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row364_fields : pairFieldsMatchB 188160 facet0 facet318 key0 key364 rowPose364 = true := by decide +kernel
theorem row364_generated : rootPair 364 = some rowPose364 :=
  pairFieldsMatchB_sound (by decide) row364_fields
theorem row364_source : sourceKey 364 ∈ geometry.profile (sourceOwner 364) := by decide +kernel
theorem row364_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 318 key0).FastValid geometry rowPose364 := by decide +kernel
theorem row364_illegal : ¬ geometry.LegalContact rowPose364 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row364_reject_checked)
theorem row364_classified : RowClassified 364 := by
  intro p generated legal
  have he : rowPose364 = p := Option.some.inj (row364_generated.symm.trans generated)
  subst p
  exact (row364_illegal legal).elim

def rowPose365 : Pose 7 := ⟨perm73, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row365_fields : pairFieldsMatchB 188160 facet0 facet319 key0 key365 rowPose365 = true := by decide +kernel
theorem row365_generated : rootPair 365 = some rowPose365 :=
  pairFieldsMatchB_sound (by decide) row365_fields
theorem row365_source : sourceKey 365 ∈ geometry.profile (sourceOwner 365) := by decide +kernel
theorem row365_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 319 key1).FastValid geometry rowPose365 := by decide +kernel
theorem row365_illegal : ¬ geometry.LegalContact rowPose365 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row365_reject_checked)
theorem row365_classified : RowClassified 365 := by
  intro p generated legal
  have he : rowPose365 = p := Option.some.inj (row365_generated.symm.trans generated)
  subst p
  exact (row365_illegal legal).elim

def rowPose366 : Pose 7 := ⟨perm87, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row366_fields : pairFieldsMatchB 188160 facet0 facet320 key0 key366 rowPose366 = true := by decide +kernel
theorem row366_generated : rootPair 366 = some rowPose366 :=
  pairFieldsMatchB_sound (by decide) row366_fields
theorem row366_source : sourceKey 366 ∈ geometry.profile (sourceOwner 366) := by decide +kernel
theorem row366_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 320 key0).FastValid geometry rowPose366 := by decide +kernel
theorem row366_illegal : ¬ geometry.LegalContact rowPose366 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row366_reject_checked)
theorem row366_classified : RowClassified 366 := by
  intro p generated legal
  have he : rowPose366 = p := Option.some.inj (row366_generated.symm.trans generated)
  subst p
  exact (row366_illegal legal).elim

def rowPose367 : Pose 7 := ⟨perm96, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row367_fields : pairFieldsMatchB 188160 facet0 facet321 key0 key367 rowPose367 = true := by decide +kernel
theorem row367_generated : rootPair 367 = some rowPose367 :=
  pairFieldsMatchB_sound (by decide) row367_fields
theorem row367_source : sourceKey 367 ∈ geometry.profile (sourceOwner 367) := by decide +kernel
theorem row367_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 321 key0).FastValid geometry rowPose367 := by decide +kernel
theorem row367_illegal : ¬ geometry.LegalContact rowPose367 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row367_reject_checked)
theorem row367_classified : RowClassified 367 := by
  intro p generated legal
  have he : rowPose367 = p := Option.some.inj (row367_generated.symm.trans generated)
  subst p
  exact (row367_illegal legal).elim

def rowPose368 : Pose 7 := ⟨perm0, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row368_fields : pairFieldsMatchB 188160 facet0 facet322 key0 key368 rowPose368 = true := by decide +kernel
theorem row368_generated : rootPair 368 = some rowPose368 :=
  pairFieldsMatchB_sound (by decide) row368_fields
theorem row368_source : sourceKey 368 ∈ geometry.profile (sourceOwner 368) := by decide +kernel
theorem row368_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 322 key1).FastValid geometry rowPose368 := by decide +kernel
theorem row368_illegal : ¬ geometry.LegalContact rowPose368 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row368_reject_checked)
theorem row368_classified : RowClassified 368 := by
  intro p generated legal
  have he : rowPose368 = p := Option.some.inj (row368_generated.symm.trans generated)
  subst p
  exact (row368_illegal legal).elim

def rowPose369 : Pose 7 := ⟨perm16, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row369_fields : pairFieldsMatchB 188160 facet0 facet323 key0 key369 rowPose369 = true := by decide +kernel
theorem row369_generated : rootPair 369 = some rowPose369 :=
  pairFieldsMatchB_sound (by decide) row369_fields
theorem row369_source : sourceKey 369 ∈ geometry.profile (sourceOwner 369) := by decide +kernel
theorem row369_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 323 key0).FastValid geometry rowPose369 := by decide +kernel
theorem row369_illegal : ¬ geometry.LegalContact rowPose369 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row369_reject_checked)
theorem row369_classified : RowClassified 369 := by
  intro p generated legal
  have he : rowPose369 = p := Option.some.inj (row369_generated.symm.trans generated)
  subst p
  exact (row369_illegal legal).elim

def rowPose370 : Pose 7 := ⟨perm40, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row370_fields : pairFieldsMatchB 188160 facet0 facet324 key0 key370 rowPose370 = true := by decide +kernel
theorem row370_generated : rootPair 370 = some rowPose370 :=
  pairFieldsMatchB_sound (by decide) row370_fields
theorem row370_source : sourceKey 370 ∈ geometry.profile (sourceOwner 370) := by decide +kernel
theorem row370_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 324 key1).FastValid geometry rowPose370 := by decide +kernel
theorem row370_illegal : ¬ geometry.LegalContact rowPose370 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row370_reject_checked)
theorem row370_classified : RowClassified 370 := by
  intro p generated legal
  have he : rowPose370 = p := Option.some.inj (row370_generated.symm.trans generated)
  subst p
  exact (row370_illegal legal).elim

def rowPose371 : Pose 7 := ⟨perm53, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row371_fields : pairFieldsMatchB 188160 facet0 facet325 key0 key371 rowPose371 = true := by decide +kernel
theorem row371_generated : rootPair 371 = some rowPose371 :=
  pairFieldsMatchB_sound (by decide) row371_fields
theorem row371_source : sourceKey 371 ∈ geometry.profile (sourceOwner 371) := by decide +kernel
theorem row371_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 325 key0).FastValid geometry rowPose371 := by decide +kernel
theorem row371_illegal : ¬ geometry.LegalContact rowPose371 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row371_reject_checked)
theorem row371_classified : RowClassified 371 := by
  intro p generated legal
  have he : rowPose371 = p := Option.some.inj (row371_generated.symm.trans generated)
  subst p
  exact (row371_illegal legal).elim

def rowPose372 : Pose 7 := ⟨perm74, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row372_fields : pairFieldsMatchB 188160 facet0 facet326 key0 key372 rowPose372 = true := by decide +kernel
theorem row372_generated : rootPair 372 = some rowPose372 :=
  pairFieldsMatchB_sound (by decide) row372_fields
theorem row372_source : sourceKey 372 ∈ geometry.profile (sourceOwner 372) := by decide +kernel
theorem row372_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 326 key0).FastValid geometry rowPose372 := by decide +kernel
theorem row372_illegal : ¬ geometry.LegalContact rowPose372 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row372_reject_checked)
theorem row372_classified : RowClassified 372 := by
  intro p generated legal
  have he : rowPose372 = p := Option.some.inj (row372_generated.symm.trans generated)
  subst p
  exact (row372_illegal legal).elim

def rowPose373 : Pose 7 := ⟨perm90, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row373_fields : pairFieldsMatchB 188160 facet0 facet327 key0 key373 rowPose373 = true := by decide +kernel
theorem row373_generated : rootPair 373 = some rowPose373 :=
  pairFieldsMatchB_sound (by decide) row373_fields
theorem row373_source : sourceKey 373 ∈ geometry.profile (sourceOwner 373) := by decide +kernel
theorem row373_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 327 key0).FastValid geometry rowPose373 := by decide +kernel
theorem row373_illegal : ¬ geometry.LegalContact rowPose373 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row373_reject_checked)
theorem row373_classified : RowClassified 373 := by
  intro p generated legal
  have he : rowPose373 = p := Option.some.inj (row373_generated.symm.trans generated)
  subst p
  exact (row373_illegal legal).elim

def rowPose374 : Pose 7 := ⟨perm87, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row374_fields : pairFieldsMatchB 188160 facet0 facet327 key0 key374 rowPose374 = true := by decide +kernel
theorem row374_generated : rootPair 374 = some rowPose374 :=
  pairFieldsMatchB_sound (by decide) row374_fields
theorem row374_source : sourceKey 374 ∈ geometry.profile (sourceOwner 374) := by decide +kernel
theorem row374_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 334 key8).FastValid geometry rowPose374 := by decide +kernel
theorem row374_illegal : ¬ geometry.LegalContact rowPose374 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row374_reject_checked)
theorem row374_classified : RowClassified 374 := by
  intro p generated legal
  have he : rowPose374 = p := Option.some.inj (row374_generated.symm.trans generated)
  subst p
  exact (row374_illegal legal).elim

def rowPose375 : Pose 7 := ⟨perm111, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row375_fields : pairFieldsMatchB 188160 facet0 facet328 key0 key375 rowPose375 = true := by decide +kernel
theorem row375_generated : rootPair 375 = some rowPose375 :=
  pairFieldsMatchB_sound (by decide) row375_fields
theorem row375_source : sourceKey 375 ∈ geometry.profile (sourceOwner 375) := by decide +kernel
theorem row375_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 328 key1).FastValid geometry rowPose375 := by decide +kernel
theorem row375_illegal : ¬ geometry.LegalContact rowPose375 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row375_reject_checked)
theorem row375_classified : RowClassified 375 := by
  intro p generated legal
  have he : rowPose375 = p := Option.some.inj (row375_generated.symm.trans generated)
  subst p
  exact (row375_illegal legal).elim

def rowPose376 : Pose 7 := ⟨perm0, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row376_fields : pairFieldsMatchB 188160 facet0 facet329 key0 key376 rowPose376 = true := by decide +kernel
theorem row376_generated : rootPair 376 = some rowPose376 :=
  pairFieldsMatchB_sound (by decide) row376_fields
theorem row376_source : sourceKey 376 ∈ geometry.profile (sourceOwner 376) := by decide +kernel
theorem row376_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 329 key1).FastValid geometry rowPose376 := by decide +kernel
theorem row376_illegal : ¬ geometry.LegalContact rowPose376 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row376_reject_checked)
theorem row376_classified : RowClassified 376 := by
  intro p generated legal
  have he : rowPose376 = p := Option.some.inj (row376_generated.symm.trans generated)
  subst p
  exact (row376_illegal legal).elim

def rowPose377 : Pose 7 := ⟨perm21, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row377_fields : pairFieldsMatchB 188160 facet0 facet330 key0 key377 rowPose377 = true := by decide +kernel
theorem row377_generated : rootPair 377 = some rowPose377 :=
  pairFieldsMatchB_sound (by decide) row377_fields
theorem row377_source : sourceKey 377 ∈ geometry.profile (sourceOwner 377) := by decide +kernel
theorem row377_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 330 key0).FastValid geometry rowPose377 := by decide +kernel
theorem row377_illegal : ¬ geometry.LegalContact rowPose377 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row377_reject_checked)
theorem row377_classified : RowClassified 377 := by
  intro p generated legal
  have he : rowPose377 = p := Option.some.inj (row377_generated.symm.trans generated)
  subst p
  exact (row377_illegal legal).elim

def rowPose378 : Pose 7 := ⟨perm24, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row378_fields : pairFieldsMatchB 188160 facet0 facet330 key0 key378 rowPose378 = true := by decide +kernel
theorem row378_generated : rootPair 378 = some rowPose378 :=
  pairFieldsMatchB_sound (by decide) row378_fields
theorem row378_source : sourceKey 378 ∈ geometry.profile (sourceOwner 378) := by decide +kernel
theorem row378_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 780 key8).FastValid geometry rowPose378 := by decide +kernel
theorem row378_illegal : ¬ geometry.LegalContact rowPose378 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row378_reject_checked)
theorem row378_classified : RowClassified 378 := by
  intro p generated legal
  have he : rowPose378 = p := Option.some.inj (row378_generated.symm.trans generated)
  subst p
  exact (row378_illegal legal).elim

def rowPose379 : Pose 7 := ⟨perm37, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row379_fields : pairFieldsMatchB 188160 facet0 facet331 key0 key379 rowPose379 = true := by decide +kernel
theorem row379_generated : rootPair 379 = some rowPose379 :=
  pairFieldsMatchB_sound (by decide) row379_fields
theorem row379_source : sourceKey 379 ∈ geometry.profile (sourceOwner 379) := by decide +kernel
theorem row379_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 331 key0).FastValid geometry rowPose379 := by decide +kernel
theorem row379_illegal : ¬ geometry.LegalContact rowPose379 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row379_reject_checked)
theorem row379_classified : RowClassified 379 := by
  intro p generated legal
  have he : rowPose379 = p := Option.some.inj (row379_generated.symm.trans generated)
  subst p
  exact (row379_illegal legal).elim

def rowPose380 : Pose 7 := ⟨perm58, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row380_fields : pairFieldsMatchB 188160 facet0 facet332 key0 key380 rowPose380 = true := by decide +kernel
theorem row380_generated : rootPair 380 = some rowPose380 :=
  pairFieldsMatchB_sound (by decide) row380_fields
theorem row380_source : sourceKey 380 ∈ geometry.profile (sourceOwner 380) := by decide +kernel
theorem row380_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 332 key0).FastValid geometry rowPose380 := by decide +kernel
theorem row380_illegal : ¬ geometry.LegalContact rowPose380 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row380_reject_checked)
theorem row380_classified : RowClassified 380 := by
  intro p generated legal
  have he : rowPose380 = p := Option.some.inj (row380_generated.symm.trans generated)
  subst p
  exact (row380_illegal legal).elim

def rowPose381 : Pose 7 := ⟨perm71, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row381_fields : pairFieldsMatchB 188160 facet0 facet333 key0 key381 rowPose381 = true := by decide +kernel
theorem row381_generated : rootPair 381 = some rowPose381 :=
  pairFieldsMatchB_sound (by decide) row381_fields
theorem row381_source : sourceKey 381 ∈ geometry.profile (sourceOwner 381) := by decide +kernel
theorem row381_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 333 key1).FastValid geometry rowPose381 := by decide +kernel
theorem row381_illegal : ¬ geometry.LegalContact rowPose381 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row381_reject_checked)
theorem row381_classified : RowClassified 381 := by
  intro p generated legal
  have he : rowPose381 = p := Option.some.inj (row381_generated.symm.trans generated)
  subst p
  exact (row381_illegal legal).elim

def rowPose382 : Pose 7 := ⟨perm95, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row382_fields : pairFieldsMatchB 188160 facet0 facet334 key0 key382 rowPose382 = true := by decide +kernel
theorem row382_generated : rootPair 382 = some rowPose382 :=
  pairFieldsMatchB_sound (by decide) row382_fields
theorem row382_source : sourceKey 382 ∈ geometry.profile (sourceOwner 382) := by decide +kernel
theorem row382_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 334 key0).FastValid geometry rowPose382 := by decide +kernel
theorem row382_illegal : ¬ geometry.LegalContact rowPose382 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row382_reject_checked)
theorem row382_classified : RowClassified 382 := by
  intro p generated legal
  have he : rowPose382 = p := Option.some.inj (row382_generated.symm.trans generated)
  subst p
  exact (row382_illegal legal).elim

def rowPose383 : Pose 7 := ⟨perm111, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row383_fields : pairFieldsMatchB 188160 facet0 facet335 key0 key383 rowPose383 = true := by decide +kernel
theorem row383_generated : rootPair 383 = some rowPose383 :=
  pairFieldsMatchB_sound (by decide) row383_fields
theorem row383_source : sourceKey 383 ∈ geometry.profile (sourceOwner 383) := by decide +kernel
theorem row383_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 335 key1).FastValid geometry rowPose383 := by decide +kernel
theorem row383_illegal : ¬ geometry.LegalContact rowPose383 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row383_reject_checked)
theorem row383_classified : RowClassified 383 := by
  intro p generated legal
  have he : rowPose383 = p := Option.some.inj (row383_generated.symm.trans generated)
  subst p
  exact (row383_illegal legal).elim

theorem chunk11_classified (i : Fin 32) : RowClassified ⟨352 + i.val, by omega⟩ := by
  fin_cases i
  · exact row352_classified
  · exact row353_classified
  · exact row354_classified
  · exact row355_classified
  · exact row356_classified
  · exact row357_classified
  · exact row358_classified
  · exact row359_classified
  · exact row360_classified
  · exact row361_classified
  · exact row362_classified
  · exact row363_classified
  · exact row364_classified
  · exact row365_classified
  · exact row366_classified
  · exact row367_classified
  · exact row368_classified
  · exact row369_classified
  · exact row370_classified
  · exact row371_classified
  · exact row372_classified
  · exact row373_classified
  · exact row374_classified
  · exact row375_classified
  · exact row376_classified
  · exact row377_classified
  · exact row378_classified
  · exact row379_classified
  · exact row380_classified
  · exact row381_classified
  · exact row382_classified
  · exact row383_classified

theorem chunk11_source (i : Fin 32) : sourceKey ⟨352 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨352 + i.val, by omega⟩) := by
  fin_cases i
  · exact row352_source
  · exact row353_source
  · exact row354_source
  · exact row355_source
  · exact row356_source
  · exact row357_source
  · exact row358_source
  · exact row359_source
  · exact row360_source
  · exact row361_source
  · exact row362_source
  · exact row363_source
  · exact row364_source
  · exact row365_source
  · exact row366_source
  · exact row367_source
  · exact row368_source
  · exact row369_source
  · exact row370_source
  · exact row371_source
  · exact row372_source
  · exact row373_source
  · exact row374_source
  · exact row375_source
  · exact row376_source
  · exact row377_source
  · exact row378_source
  · exact row379_source
  · exact row380_source
  · exact row381_source
  · exact row382_source
  · exact row383_source

#print axioms chunk11_classified
end SparseMonotiles.Contact.RootZeroPilot7
