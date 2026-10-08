module
public import SparseMonotiles.T7AutomaticSparseRows
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7SiblingData
open Contact Existence.Catalog7World T7SparseForwardBlock T7GlobalSparseAssembly
open T7GeneratedForwardAssembly T7AutomaticSparseRows
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- These are only proposed catalog indices. Values on ungenerated roles do not matter.
-- Every used full-pose equality is reduced by the kernel in siblings_checked.
def siblingMate0 (b : Fin 128) : Fin 408 :=
  (if b.val < 16 then (if b.val < 4 then (if b.val < 2 then 217 else 265) else (if b.val < 8 then 293 else 320)) else (if b.val < 64 then (if b.val < 32 then 349 else 375) else (if b.val < 127 then 407 else 239)))

def siblingMate1 (b : Fin 128) : Fin 408 :=
  (if b.val < 17 then (if b.val < 5 then (if b.val < 3 then 217 else 323) else (if b.val < 9 then 405 else 297)) else (if b.val < 65 then (if b.val < 33 then 371 else 267) else (if b.val < 127 then 341 else 216)))

def siblingMate2 (b : Fin 128) : Fin 408 :=
  (if b.val < 18 then (if b.val < 6 then (if b.val < 3 then 180 else 341) else (if b.val < 10 then 323 else 405)) else (if b.val < 66 then (if b.val < 34 then 297 else 371) else (if b.val < 127 then 267 else 179)))

def siblingMate3 (b : Fin 128) : Fin 408 :=
  (if b.val < 19 then (if b.val < 7 then (if b.val < 2 then 321 else 347) else (if b.val < 11 then 350 else 299)) else (if b.val < 67 then (if b.val < 35 then 217 else 368) else (if b.val < 127 then 317 else 355)))

def siblingMate4 (b : Fin 128) : Fin 408 :=
  (if b.val < 20 then (if b.val < 6 then (if b.val < 5 then 148 else 267) else (if b.val < 12 then 341 else 323)) else (if b.val < 68 then (if b.val < 36 then 405 else 297) else (if b.val < 127 then 371 else 147)))

def siblingMate5 (b : Fin 128) : Fin 408 :=
  (if b.val < 21 then (if b.val < 7 then (if b.val < 4 then 385 else 272) else (if b.val < 13 then 217 else 317)) else (if b.val < 69 then (if b.val < 37 then 269 else 404) else (if b.val < 127 then 350 else 259)))

def siblingMate6 (b : Fin 128) : Fin 408 :=
  (if b.val < 22 then (if b.val < 7 then (if b.val < 4 then 321 else 347) else (if b.val < 14 then 317 else 350)) else (if b.val < 70 then (if b.val < 38 then 299 else 217) else (if b.val < 127 then 368 else 380)))

def siblingMate7 (b : Fin 128) : Fin 408 :=
  (if b.val < 23 then (if b.val < 6 then (if b.val < 5 then 351 else 217) else (if b.val < 15 then 315 else 322)) else (if b.val < 71 then (if b.val < 39 then 270 else 403) else (if b.val < 127 then 344 else 174)))

def siblingMate8 (b : Fin 128) : Fin 408 :=
  (if b.val < 24 then (if b.val < 10 then (if b.val < 9 then 119 else 371) else (if b.val < 12 then 267 else 341)) else (if b.val < 72 then (if b.val < 40 then 323 else 405) else (if b.val < 127 then 297 else 118)))

def siblingMate9 (b : Fin 128) : Fin 408 :=
  (if b.val < 25 then (if b.val < 11 then (if b.val < 8 then 298 else 369) else (if b.val < 13 then 269 else 404)) else (if b.val < 73 then (if b.val < 41 then 299 else 217) else (if b.val < 127 then 368 else 379)))

def siblingMate10 (b : Fin 128) : Fin 408 :=
  (if b.val < 26 then (if b.val < 11 then (if b.val < 8 then 385 else 272) else (if b.val < 14 then 350 else 217)) else (if b.val < 74 then (if b.val < 42 then 317 else 269) else (if b.val < 127 then 404 else 286)))

def siblingMate11 (b : Fin 128) : Fin 408 :=
  (if b.val < 27 then (if b.val < 10 then (if b.val < 9 then 296 else 271) else (if b.val < 15 then 351 else 270)) else (if b.val < 75 then (if b.val < 43 then 344 else 290) else (if b.val < 127 then 217 else 402)))

def siblingMate12 (b : Fin 128) : Fin 408 :=
  (if b.val < 28 then (if b.val < 13 then (if b.val < 8 then 321 else 347) else (if b.val < 14 then 368 else 317)) else (if b.val < 76 then (if b.val < 44 then 350 else 299) else (if b.val < 127 then 217 else 396)))

def siblingMate13 (b : Fin 128) : Fin 408 :=
  (if b.val < 29 then (if b.val < 12 then (if b.val < 9 then 315 else 401) else (if b.val < 15 then 373 else 403)) else (if b.val < 77 then (if b.val < 45 then 217 else 376) else (if b.val < 127 then 322 else 339)))

def siblingMate14 (b : Fin 128) : Fin 408 :=
  (if b.val < 30 then (if b.val < 12 then (if b.val < 10 then 351 else 217) else (if b.val < 15 then 315 else 344)) else (if b.val < 78 then (if b.val < 46 then 322 else 270) else (if b.val < 127 then 403 else 141)))

def siblingMate15 (b : Fin 128) : Fin 408 :=
  (if b.val < 31 then (if b.val < 13 then (if b.val < 11 then 322 else 270) else (if b.val < 14 then 403 else 344)) else (if b.val < 79 then (if b.val < 47 then 351 else 217) else (if b.val < 127 then 315 else 377)))

def siblingMate16 (b : Fin 128) : Fin 408 :=
  (if b.val < 24 then (if b.val < 18 then (if b.val < 17 then 86 else 297) else (if b.val < 20 then 371 else 267)) else (if b.val < 80 then (if b.val < 48 then 341 else 323) else (if b.val < 127 then 405 else 85)))

def siblingMate17 (b : Fin 128) : Fin 408 :=
  (if b.val < 25 then (if b.val < 19 then (if b.val < 16 then 369 else 298) else (if b.val < 21 then 299 else 217)) else (if b.val < 81 then (if b.val < 49 then 368 else 269) else (if b.val < 127 then 404 else 301)))

def siblingMate18 (b : Fin 128) : Fin 408 :=
  (if b.val < 26 then (if b.val < 19 then (if b.val < 16 then 298 else 369) else (if b.val < 22 then 368 else 269)) else (if b.val < 82 then (if b.val < 50 then 404 else 299) else (if b.val < 127 then 217 else 394)))

def siblingMate19 (b : Fin 128) : Fin 408 :=
  (if b.val < 27 then (if b.val < 18 then (if b.val < 17 then 217 else 296) else (if b.val < 23 then 373 else 344)) else (if b.val < 83 then (if b.val < 51 then 290 else 376) else (if b.val < 127 then 322 else 84)))

def siblingMate20 (b : Fin 128) : Fin 408 :=
  (if b.val < 28 then (if b.val < 21 then (if b.val < 16 then 385 else 272) else (if b.val < 22 then 404 else 350)) else (if b.val < 84 then (if b.val < 52 then 217 else 317) else (if b.val < 127 then 269 else 310)))

def siblingMate21 (b : Fin 128) : Fin 408 :=
  (if b.val < 29 then (if b.val < 20 then (if b.val < 17 then 271 else 217) else (if b.val < 23 then 401 else 290)) else (if b.val < 85 then (if b.val < 53 then 376 else 270) else (if b.val < 127 then 403 else 145)))

def siblingMate22 (b : Fin 128) : Fin 408 :=
  (if b.val < 30 then (if b.val < 20 then (if b.val < 18 then 296 else 271) else (if b.val < 23 then 351 else 217)) else (if b.val < 86 then (if b.val < 54 then 270 else 344) else (if b.val < 127 then 290 else 243)))

def siblingMate23 (b : Fin 128) : Fin 408 :=
  (if b.val < 31 then (if b.val < 21 then (if b.val < 19 then 270 else 344) else (if b.val < 22 then 290 else 217)) else (if b.val < 87 then (if b.val < 55 then 296 else 271) else (if b.val < 127 then 351 else 201)))

def siblingMate24 (b : Fin 128) : Fin 408 :=
  (if b.val < 28 then (if b.val < 25 then (if b.val < 16 then 321 else 347) else (if b.val < 26 then 217 else 368)) else (if b.val < 88 then (if b.val < 56 then 317 else 350) else (if b.val < 127 then 299 else 237)))

def siblingMate25 (b : Fin 128) : Fin 408 :=
  (if b.val < 29 then (if b.val < 24 then (if b.val < 17 then 296 else 373) else (if b.val < 27 then 217 else 376)) else (if b.val < 89 then (if b.val < 57 then 322 else 344) else (if b.val < 127 then 290 else 213)))

def siblingMate26 (b : Fin 128) : Fin 408 :=
  (if b.val < 30 then (if b.val < 24 then (if b.val < 18 then 315 else 401) else (if b.val < 27 then 373 else 322)) else (if b.val < 90 then (if b.val < 58 then 403 else 217) else (if b.val < 127 then 376 else 365)))

def siblingMate27 (b : Fin 128) : Fin 408 :=
  (if b.val < 31 then (if b.val < 25 then (if b.val < 19 then 344 else 290) else (if b.val < 26 then 376 else 322)) else (if b.val < 91 then (if b.val < 59 then 217 else 296) else (if b.val < 127 then 373 else 282)))

def siblingMate28 (b : Fin 128) : Fin 408 :=
  (if b.val < 30 then (if b.val < 24 then (if b.val < 20 then 351 else 217) else (if b.val < 29 then 315 else 403)) else (if b.val < 92 then (if b.val < 60 then 344 else 322) else (if b.val < 127 then 270 else 111)))

def siblingMate29 (b : Fin 128) : Fin 408 :=
  (if b.val < 31 then (if b.val < 25 then (if b.val < 21 then 217 else 376) else (if b.val < 28 then 322 else 403)) else (if b.val < 93 then (if b.val < 61 then 373 else 315) else (if b.val < 127 then 401 else 91)))

def siblingMate30 (b : Fin 128) : Fin 408 :=
  (if b.val < 31 then (if b.val < 26 then (if b.val < 22 then 322 else 270) else (if b.val < 28 then 403 else 344)) else (if b.val < 94 then (if b.val < 62 then 315 else 351) else (if b.val < 127 then 217 else 393)))

def siblingMate31 (b : Fin 128) : Fin 408 :=
  (if b.val < 30 then (if b.val < 27 then (if b.val < 23 then 350 else 299) else (if b.val < 29 then 217 else 368)) else (if b.val < 95 then (if b.val < 63 then 317 else 321) else (if b.val < 127 then 347 else 138)))

def siblingMate32 (b : Fin 128) : Fin 408 :=
  (if b.val < 40 then (if b.val < 34 then (if b.val < 33 then 56 else 405) else (if b.val < 36 then 297 else 371)) else (if b.val < 96 then (if b.val < 48 then 267 else 341) else (if b.val < 127 then 323 else 55)))

def siblingMate33 (b : Fin 128) : Fin 408 :=
  (if b.val < 41 then (if b.val < 35 then (if b.val < 32 then 272 else 385) else (if b.val < 37 then 317 else 269)) else (if b.val < 97 then (if b.val < 49 then 404 else 350) else (if b.val < 127 then 217 else 392)))

def siblingMate34 (b : Fin 128) : Fin 408 :=
  (if b.val < 42 then (if b.val < 35 then (if b.val < 32 then 369 else 298) else (if b.val < 38 then 404 else 299)) else (if b.val < 98 then (if b.val < 50 then 217 else 368) else (if b.val < 127 then 269 else 326)))

def siblingMate35 (b : Fin 128) : Fin 408 :=
  (if b.val < 43 then (if b.val < 34 then (if b.val < 33 then 373 else 315) else (if b.val < 39 then 401 else 217)) else (if b.val < 99 then (if b.val < 51 then 376 else 322) else (if b.val < 127 then 403 else 289)))

def siblingMate36 (b : Fin 128) : Fin 408 :=
  (if b.val < 44 then (if b.val < 37 then (if b.val < 32 then 298 else 369) else (if b.val < 38 then 217 else 368)) else (if b.val < 100 then (if b.val < 52 then 269 else 404) else (if b.val < 127 then 299 else 235)))

def siblingMate37 (b : Fin 128) : Fin 408 :=
  (if b.val < 45 then (if b.val < 36 then (if b.val < 33 then 401 else 271) else (if b.val < 39 then 217 else 376)) else (if b.val < 101 then (if b.val < 53 then 270 else 403) else (if b.val < 127 then 290 else 211)))

def siblingMate38 (b : Fin 128) : Fin 408 :=
  (if b.val < 46 then (if b.val < 36 then (if b.val < 34 then 217 else 296) else (if b.val < 39 then 373 else 322)) else (if b.val < 102 then (if b.val < 54 then 344 else 290) else (if b.val < 127 then 376 else 53)))

def siblingMate39 (b : Fin 128) : Fin 408 :=
  (if b.val < 47 then (if b.val < 37 then (if b.val < 35 then 403 else 217) else (if b.val < 38 then 376 else 322)) else (if b.val < 103 then (if b.val < 55 then 315 else 401) else (if b.val < 127 then 373 else 153)))

def siblingMate40 (b : Fin 128) : Fin 408 :=
  (if b.val < 44 then (if b.val < 41 then (if b.val < 32 then 385 else 272) else (if b.val < 42 then 269 else 404)) else (if b.val < 104 then (if b.val < 56 then 350 else 217) else (if b.val < 127 then 317 else 338)))

def siblingMate41 (b : Fin 128) : Fin 408 :=
  (if b.val < 45 then (if b.val < 40 then (if b.val < 33 then 217 else 401) else (if b.val < 43 then 271 else 270)) else (if b.val < 105 then (if b.val < 57 then 403 else 290) else (if b.val < 127 then 376 else 50)))

def siblingMate42 (b : Fin 128) : Fin 408 :=
  (if b.val < 46 then (if b.val < 40 then (if b.val < 34 then 271 else 217) else (if b.val < 43 then 401 else 403)) else (if b.val < 106 then (if b.val < 58 then 290 else 376) else (if b.val < 127 then 270 else 114)))

def siblingMate43 (b : Fin 128) : Fin 408 :=
  (if b.val < 47 then (if b.val < 41 then (if b.val < 35 then 290 else 376) else (if b.val < 42 then 270 else 403)) else (if b.val < 107 then (if b.val < 59 then 271 else 217) else (if b.val < 127 then 401 else 336)))

def siblingMate44 (b : Fin 128) : Fin 408 :=
  (if b.val < 46 then (if b.val < 40 then (if b.val < 36 then 296 else 271) else (if b.val < 45 then 351 else 290)) else (if b.val < 108 then (if b.val < 60 then 217 else 270) else (if b.val < 127 then 344 else 268)))

def siblingMate45 (b : Fin 128) : Fin 408 :=
  (if b.val < 47 then (if b.val < 41 then (if b.val < 37 then 376 else 270) else (if b.val < 44 then 403 else 290)) else (if b.val < 109 then (if b.val < 61 then 401 else 271) else (if b.val < 127 then 217 else 391)))

def siblingMate46 (b : Fin 128) : Fin 408 :=
  (if b.val < 47 then (if b.val < 42 then (if b.val < 38 then 270 else 344) else (if b.val < 44 then 290 else 217)) else (if b.val < 110 then (if b.val < 62 then 351 else 296) else (if b.val < 127 then 271 else 164)))

def siblingMate47 (b : Fin 128) : Fin 408 :=
  (if b.val < 46 then (if b.val < 43 then (if b.val < 39 then 217 else 317) else (if b.val < 45 then 269 else 404)) else (if b.val < 111 then (if b.val < 63 then 350 else 385) else (if b.val < 127 then 272 else 49)))

def siblingMate48 (b : Fin 128) : Fin 408 :=
  (if b.val < 52 then (if b.val < 49 then (if b.val < 32 then 321 else 347) else (if b.val < 50 then 299 else 217)) else (if b.val < 112 then (if b.val < 56 then 368 else 317) else (if b.val < 127 then 350 else 277)))

def siblingMate49 (b : Fin 128) : Fin 408 :=
  (if b.val < 53 then (if b.val < 48 then (if b.val < 33 then 271 else 351) else (if b.val < 51 then 296 else 344)) else (if b.val < 113 then (if b.val < 57 then 290 else 217) else (if b.val < 127 then 270 else 318)))

def siblingMate50 (b : Fin 128) : Fin 408 :=
  (if b.val < 54 then (if b.val < 48 then (if b.val < 34 then 296 else 373) else (if b.val < 51 then 217 else 290)) else (if b.val < 114 then (if b.val < 58 then 376 else 322) else (if b.val < 127 then 344 else 177)))

def siblingMate51 (b : Fin 128) : Fin 408 :=
  (if b.val < 55 then (if b.val < 49 then (if b.val < 35 then 376 else 322) else (if b.val < 50 then 344 else 290)) else (if b.val < 115 then (if b.val < 59 then 296 else 373) else (if b.val < 127 then 217 else 390)))

def siblingMate52 (b : Fin 128) : Fin 408 :=
  (if b.val < 54 then (if b.val < 48 then (if b.val < 36 then 315 else 401) else (if b.val < 53 then 373 else 376)) else (if b.val < 116 then (if b.val < 60 then 322 else 403) else (if b.val < 127 then 217 else 383)))

def siblingMate53 (b : Fin 128) : Fin 408 :=
  (if b.val < 55 then (if b.val < 49 then (if b.val < 37 then 270 else 403) else (if b.val < 52 then 290 else 376)) else (if b.val < 117 then (if b.val < 61 then 217 else 401) else (if b.val < 127 then 271 else 257)))

def siblingMate54 (b : Fin 128) : Fin 408 :=
  (if b.val < 55 then (if b.val < 50 then (if b.val < 38 then 344 else 290) else (if b.val < 52 then 376 else 322)) else (if b.val < 118 then (if b.val < 62 then 373 else 217) else (if b.val < 127 then 296 else 307)))

def siblingMate55 (b : Fin 128) : Fin 408 :=
  (if b.val < 54 then (if b.val < 51 then (if b.val < 39 then 269 else 404) else (if b.val < 53 then 299 else 217)) else (if b.val < 119 then (if b.val < 63 then 368 else 298) else (if b.val < 127 then 369 else 173)))

def siblingMate56 (b : Fin 128) : Fin 408 :=
  (if b.val < 58 then (if b.val < 48 then (if b.val < 40 then 351 else 217) else (if b.val < 57 then 315 else 270)) else (if b.val < 120 then (if b.val < 60 then 403 else 344) else (if b.val < 127 then 322 else 80)))

def siblingMate57 (b : Fin 128) : Fin 408 :=
  (if b.val < 59 then (if b.val < 49 then (if b.val < 41 then 344 else 290) else (if b.val < 56 then 217 else 270)) else (if b.val < 121 then (if b.val < 61 then 271 else 351) else (if b.val < 127 then 296 else 102)))

def siblingMate58 (b : Fin 128) : Fin 408 :=
  (if b.val < 59 then (if b.val < 50 then (if b.val < 42 then 217 else 376) else (if b.val < 56 then 322 else 403)) else (if b.val < 122 then (if b.val < 62 then 401 else 373) else (if b.val < 127 then 315 else 59)))

def siblingMate59 (b : Fin 128) : Fin 408 :=
  (if b.val < 58 then (if b.val < 51 then (if b.val < 43 then 299 else 217) else (if b.val < 57 then 368 else 269)) else (if b.val < 123 then (if b.val < 63 then 404 else 369) else (if b.val < 127 then 298 else 78)))

def siblingMate60 (b : Fin 128) : Fin 408 :=
  (if b.val < 61 then (if b.val < 52 then (if b.val < 44 then 322 else 270) else (if b.val < 56 then 403 else 344)) else (if b.val < 124 then (if b.val < 62 then 217 else 315) else (if b.val < 127 then 351 else 233)))

def siblingMate61 (b : Fin 128) : Fin 408 :=
  (if b.val < 60 then (if b.val < 53 then (if b.val < 45 then 317 else 269) else (if b.val < 57 then 404 else 350)) else (if b.val < 125 then (if b.val < 63 then 217 else 272) else (if b.val < 127 then 385 else 209)))

def siblingMate62 (b : Fin 128) : Fin 408 :=
  (if b.val < 60 then (if b.val < 54 then (if b.val < 46 then 350 else 299) else (if b.val < 58 then 217 else 368)) else (if b.val < 126 then (if b.val < 63 then 317 else 347) else (if b.val < 127 then 321 else 108)))

def siblingMate63 (b : Fin 128) : Fin 408 :=
  (if b.val < 59 then (if b.val < 47 then 323 else (if b.val < 55 then 405 else 297)) else (if b.val < 62 then (if b.val < 61 then 371 else 267) else (if b.val < 127 then 341 else 387)))

def siblingMate64 (b : Fin 128) : Fin 408 :=
  (if b.val < 72 then (if b.val < 66 then (if b.val < 65 then 30 else 323) else (if b.val < 68 then 405 else 297)) else (if b.val < 96 then (if b.val < 80 then 371 else 267) else (if b.val < 127 then 341 else 29)))

def siblingMate65 (b : Fin 128) : Fin 408 :=
  (if b.val < 73 then (if b.val < 67 then (if b.val < 64 then 347 else 321) else (if b.val < 69 then 350 else 299)) else (if b.val < 97 then (if b.val < 81 then 217 else 368) else (if b.val < 127 then 317 else 328)))

def siblingMate66 (b : Fin 128) : Fin 408 :=
  (if b.val < 74 then (if b.val < 67 then (if b.val < 64 then 272 else 385) else (if b.val < 70 then 217 else 317)) else (if b.val < 98 then (if b.val < 82 then 269 else 404) else (if b.val < 127 then 350 else 231)))

def siblingMate67 (b : Fin 128) : Fin 408 :=
  (if b.val < 75 then (if b.val < 66 then (if b.val < 65 then 315 else 351) else (if b.val < 71 then 217 else 322)) else (if b.val < 99 then (if b.val < 83 then 270 else 403) else (if b.val < 127 then 344 else 191)))

def siblingMate68 (b : Fin 128) : Fin 408 :=
  (if b.val < 76 then (if b.val < 69 then (if b.val < 64 then 369 else 298) else (if b.val < 70 then 269 else 404)) else (if b.val < 100 then (if b.val < 84 then 299 else 217) else (if b.val < 127 then 368 else 354)))

def siblingMate69 (b : Fin 128) : Fin 408 :=
  (if b.val < 77 then (if b.val < 68 then (if b.val < 65 then 351 else 296) else (if b.val < 71 then 271 else 270)) else (if b.val < 101 then (if b.val < 85 then 344 else 290) else (if b.val < 127 then 217 else 370)))

def siblingMate70 (b : Fin 128) : Fin 408 :=
  (if b.val < 78 then (if b.val < 68 then (if b.val < 66 then 373 else 315) else (if b.val < 71 then 401 else 403)) else (if b.val < 102 then (if b.val < 86 then 217 else 376) else (if b.val < 127 then 322 else 312)))

def siblingMate71 (b : Fin 128) : Fin 408 :=
  (if b.val < 79 then (if b.val < 69 then (if b.val < 67 then 344 else 322) else (if b.val < 70 then 270 else 403)) else (if b.val < 103 then (if b.val < 87 then 351 else 217) else (if b.val < 127 then 315 else 352)))

def siblingMate72 (b : Fin 128) : Fin 408 :=
  (if b.val < 76 then (if b.val < 73 then (if b.val < 64 then 298 else 369) else (if b.val < 74 then 299 else 217)) else (if b.val < 104 then (if b.val < 88 then 368 else 269) else (if b.val < 127 then 404 else 276)))

def siblingMate73 (b : Fin 128) : Fin 408 :=
  (if b.val < 77 then (if b.val < 72 then (if b.val < 65 then 373 else 217) else (if b.val < 75 then 296 else 344)) else (if b.val < 105 then (if b.val < 89 then 290 else 376) else (if b.val < 127 then 322 else 115)))

def siblingMate74 (b : Fin 128) : Fin 408 :=
  (if b.val < 78 then (if b.val < 72 then (if b.val < 66 then 401 else 271) else (if b.val < 75 then 217 else 290)) else (if b.val < 106 then (if b.val < 90 then 376 else 270) else (if b.val < 127 then 403 else 176)))

def siblingMate75 (b : Fin 128) : Fin 408 :=
  (if b.val < 79 then (if b.val < 73 then (if b.val < 67 then 217 else 270) else (if b.val < 74 then 344 else 290)) else (if b.val < 107 then (if b.val < 91 then 296 else 271) else (if b.val < 127 then 351 else 13)))

def siblingMate76 (b : Fin 128) : Fin 408 :=
  (if b.val < 78 then (if b.val < 72 then (if b.val < 68 then 217 else 296) else (if b.val < 77 then 373 else 376)) else (if b.val < 108 then (if b.val < 92 then 322 else 344) else (if b.val < 127 then 290 else 27)))

def siblingMate77 (b : Fin 128) : Fin 408 :=
  (if b.val < 79 then (if b.val < 73 then (if b.val < 69 then 322 else 344) else (if b.val < 76 then 290 else 376)) else (if b.val < 109 then (if b.val < 93 then 217 else 296) else (if b.val < 127 then 373 else 256)))

def siblingMate78 (b : Fin 128) : Fin 408 :=
  (if b.val < 79 then (if b.val < 74 then (if b.val < 70 then 403 else 217) else (if b.val < 76 then 376 else 322)) else (if b.val < 110 then (if b.val < 94 then 373 else 315) else (if b.val < 127 then 401 else 123)))

def siblingMate79 (b : Fin 128) : Fin 408 :=
  (if b.val < 78 then (if b.val < 75 then (if b.val < 71 then 317 else 350) else (if b.val < 77 then 299 else 217)) else (if b.val < 111 then (if b.val < 95 then 368 else 321) else (if b.val < 127 then 347 else 171)))

def siblingMate80 (b : Fin 128) : Fin 408 :=
  (if b.val < 84 then (if b.val < 81 then (if b.val < 64 then 385 else 272) else (if b.val < 82 then 317 else 269)) else (if b.val < 112 then (if b.val < 88 then 404 else 350) else (if b.val < 127 then 217 else 363)))

def siblingMate81 (b : Fin 128) : Fin 408 :=
  (if b.val < 85 then (if b.val < 80 then (if b.val < 65 then 401 else 373) else (if b.val < 83 then 315 else 217)) else (if b.val < 113 then (if b.val < 89 then 376 else 322) else (if b.val < 127 then 403 else 260)))

def siblingMate82 (b : Fin 128) : Fin 408 :=
  (if b.val < 86 then (if b.val < 80 then (if b.val < 66 then 217 else 401) else (if b.val < 83 then 271 else 376)) else (if b.val < 114 then (if b.val < 90 then 270 else 403) else (if b.val < 127 then 290 else 26)))

def siblingMate83 (b : Fin 128) : Fin 408 :=
  (if b.val < 87 then (if b.val < 81 then (if b.val < 67 then 322 else 403) else (if b.val < 82 then 217 else 376)) else (if b.val < 115 then (if b.val < 91 then 315 else 401) else (if b.val < 127 then 373 else 184)))

def siblingMate84 (b : Fin 128) : Fin 408 :=
  (if b.val < 86 then (if b.val < 80 then (if b.val < 68 then 271 else 217) else (if b.val < 85 then 401 else 270)) else (if b.val < 116 then (if b.val < 92 then 403 else 290) else (if b.val < 127 then 376 else 83)))

def siblingMate85 (b : Fin 128) : Fin 408 :=
  (if b.val < 87 then (if b.val < 81 then (if b.val < 69 then 403 else 290) else (if b.val < 84 then 376 else 270)) else (if b.val < 117 then (if b.val < 93 then 271 else 217) else (if b.val < 127 then 401 else 308)))

def siblingMate86 (b : Fin 128) : Fin 408 :=
  (if b.val < 87 then (if b.val < 82 then (if b.val < 70 then 290 else 376) else (if b.val < 84 then 270 else 403)) else (if b.val < 118 then (if b.val < 94 then 401 else 271) else (if b.val < 127 then 217 else 360)))

def siblingMate87 (b : Fin 128) : Fin 408 :=
  (if b.val < 86 then (if b.val < 83 then (if b.val < 71 then 350 else 217) else (if b.val < 85 then 317 else 269)) else (if b.val < 119 then (if b.val < 95 then 404 else 385) else (if b.val < 127 then 272 else 81)))

def siblingMate88 (b : Fin 128) : Fin 408 :=
  (if b.val < 90 then (if b.val < 80 then (if b.val < 72 then 296 else 271) else (if b.val < 89 then 351 else 344)) else (if b.val < 120 then (if b.val < 92 then 290 else 217) else (if b.val < 127 then 270 else 295)))

def siblingMate89 (b : Fin 128) : Fin 408 :=
  (if b.val < 91 then (if b.val < 81 then (if b.val < 73 then 290 else 376) else (if b.val < 88 then 322 else 344)) else (if b.val < 121 then (if b.val < 93 then 296 else 373) else (if b.val < 127 then 217 else 359)))

def siblingMate90 (b : Fin 128) : Fin 408 :=
  (if b.val < 91 then (if b.val < 82 then (if b.val < 74 then 376 else 270) else (if b.val < 88 then 403 else 290)) else (if b.val < 122 then (if b.val < 94 then 217 else 401) else (if b.val < 127 then 271 else 229)))

def siblingMate91 (b : Fin 128) : Fin 408 :=
  (if b.val < 90 then (if b.val < 83 then (if b.val < 75 then 368 else 269) else (if b.val < 89 then 404 else 299)) else (if b.val < 123 then (if b.val < 95 then 217 else 298) else (if b.val < 127 then 369 else 189)))

def siblingMate92 (b : Fin 128) : Fin 408 :=
  (if b.val < 93 then (if b.val < 84 then (if b.val < 76 then 270 else 344) else (if b.val < 88 then 290 else 217)) else (if b.val < 124 then (if b.val < 94 then 271 else 351) else (if b.val < 127 then 296 else 134)))

def siblingMate93 (b : Fin 128) : Fin 408 :=
  (if b.val < 92 then (if b.val < 85 then (if b.val < 77 then 404 else 299) else (if b.val < 89 then 217 else 368)) else (if b.val < 125 then (if b.val < 95 then 269 else 369) else (if b.val < 127 then 298 else 109)))

def siblingMate94 (b : Fin 128) : Fin 408 :=
  (if b.val < 92 then (if b.val < 86 then (if b.val < 78 then 217 else 317) else (if b.val < 90 then 269 else 404)) else (if b.val < 126 then (if b.val < 95 then 350 else 272) else (if b.val < 127 then 385 else 24)))

def siblingMate95 (b : Fin 128) : Fin 408 :=
  (if b.val < 91 then (if b.val < 79 then 341 else (if b.val < 87 then 323 else 405)) else (if b.val < 94 then (if b.val < 93 then 297 else 371) else (if b.val < 127 then 267 else 357)))

def siblingMate96 (b : Fin 128) : Fin 408 :=
  (if b.val < 100 then (if b.val < 97 then (if b.val < 64 then 321 else 347) else (if b.val < 98 then 350 else 299)) else (if b.val < 112 then (if b.val < 104 then 217 else 368) else (if b.val < 127 then 317 else 302)))

def siblingMate97 (b : Fin 128) : Fin 408 :=
  (if b.val < 101 then (if b.val < 96 then (if b.val < 65 then 217 else 315) else (if b.val < 99 then 351 else 322)) else (if b.val < 113 then (if b.val < 105 then 270 else 403) else (if b.val < 127 then 344 else 4)))

def siblingMate98 (b : Fin 128) : Fin 408 :=
  (if b.val < 102 then (if b.val < 96 then (if b.val < 66 then 271 else 351) else (if b.val < 99 then 296 else 270)) else (if b.val < 114 then (if b.val < 106 then 344 else 290) else (if b.val < 127 then 217 else 346)))

def siblingMate99 (b : Fin 128) : Fin 408 :=
  (if b.val < 103 then (if b.val < 97 then (if b.val < 67 then 403 else 344) else (if b.val < 98 then 322 else 270)) else (if b.val < 115 then (if b.val < 107 then 351 else 217) else (if b.val < 127 then 315 else 324)))

def siblingMate100 (b : Fin 128) : Fin 408 :=
  (if b.val < 102 then (if b.val < 96 then (if b.val < 68 then 296 else 373) else (if b.val < 101 then 217 else 344)) else (if b.val < 116 then (if b.val < 108 then 290 else 376) else (if b.val < 127 then 322 else 146)))

def siblingMate101 (b : Fin 128) : Fin 408 :=
  (if b.val < 103 then (if b.val < 97 then (if b.val < 69 then 290 else 217) else (if b.val < 100 then 270 else 344)) else (if b.val < 117 then (if b.val < 109 then 296 else 271) else (if b.val < 127 then 351 else 39)))

def siblingMate102 (b : Fin 128) : Fin 408 :=
  (if b.val < 103 then (if b.val < 98 then (if b.val < 70 then 376 else 322) else (if b.val < 100 then 344 else 290)) else (if b.val < 118 then (if b.val < 110 then 217 else 296) else (if b.val < 127 then 373 else 227)))

def siblingMate103 (b : Fin 128) : Fin 408 :=
  (if b.val < 102 then (if b.val < 99 then (if b.val < 71 then 368 else 317) else (if b.val < 101 then 350 else 299)) else (if b.val < 119 then (if b.val < 111 then 217 else 321) else (if b.val < 127 then 347 else 187)))

def siblingMate104 (b : Fin 128) : Fin 408 :=
  (if b.val < 106 then (if b.val < 96 then (if b.val < 72 then 315 else 401) else (if b.val < 105 then 373 else 217)) else (if b.val < 120 then (if b.val < 108 then 376 else 322) else (if b.val < 127 then 403 else 219)))

def siblingMate105 (b : Fin 128) : Fin 408 :=
  (if b.val < 107 then (if b.val < 97 then (if b.val < 73 then 376 else 322) else (if b.val < 104 then 403 else 217)) else (if b.val < 121 then (if b.val < 109 then 315 else 401) else (if b.val < 127 then 373 else 207)))

def siblingMate106 (b : Fin 128) : Fin 408 :=
  (if b.val < 107 then (if b.val < 98 then (if b.val < 74 then 270 else 403) else (if b.val < 104 then 290 else 376)) else (if b.val < 122 then (if b.val < 110 then 271 else 217) else (if b.val < 127 then 401 else 285)))

def siblingMate107 (b : Fin 128) : Fin 408 :=
  (if b.val < 106 then (if b.val < 99 then (if b.val < 75 then 404 else 350) else (if b.val < 105 then 217 else 317)) else (if b.val < 123 then (if b.val < 111 then 269 else 385) else (if b.val < 127 then 272 else 112)))

def siblingMate108 (b : Fin 128) : Fin 408 :=
  (if b.val < 109 then (if b.val < 100 then (if b.val < 76 then 344 else 290) else (if b.val < 104 then 376 else 322)) else (if b.val < 124 then (if b.val < 110 then 296 else 373) else (if b.val < 127 then 217 else 335)))

def siblingMate109 (b : Fin 128) : Fin 408 :=
  (if b.val < 108 then (if b.val < 101 then (if b.val < 77 then 217 else 368) else (if b.val < 105 then 269 else 404)) else (if b.val < 125 then (if b.val < 111 then 299 else 298) else (if b.val < 127 then 369 else 1)))

def siblingMate110 (b : Fin 128) : Fin 408 :=
  (if b.val < 108 then (if b.val < 102 then (if b.val < 78 then 269 else 404) else (if b.val < 106 then 299 else 217)) else (if b.val < 126 then (if b.val < 111 then 368 else 369) else (if b.val < 127 then 298 else 139)))

def siblingMate111 (b : Fin 128) : Fin 408 :=
  (if b.val < 107 then (if b.val < 79 then 267 else (if b.val < 103 then 341 else 323)) else (if b.val < 110 then (if b.val < 109 then 405 else 297) else (if b.val < 127 then 371 else 331)))

def siblingMate112 (b : Fin 128) : Fin 408 :=
  (if b.val < 114 then (if b.val < 96 then (if b.val < 80 then 351 else 217) else (if b.val < 113 then 315 else 322)) else (if b.val < 120 then (if b.val < 116 then 270 else 403) else (if b.val < 127 then 344 else 48)))

def siblingMate113 (b : Fin 128) : Fin 408 :=
  (if b.val < 115 then (if b.val < 97 then (if b.val < 81 then 270 else 403) else (if b.val < 112 then 344 else 322)) else (if b.val < 121 then (if b.val < 117 then 351 else 217) else (if b.val < 127 then 315 else 300)))

def siblingMate114 (b : Fin 128) : Fin 408 :=
  (if b.val < 115 then (if b.val < 98 then (if b.val < 82 then 344 else 290) else (if b.val < 112 then 217 else 270)) else (if b.val < 122 then (if b.val < 118 then 296 else 271) else (if b.val < 127 then 351 else 71)))

def siblingMate115 (b : Fin 128) : Fin 408 :=
  (if b.val < 114 then (if b.val < 99 then (if b.val < 83 then 217 else 368) else (if b.val < 113 then 317 else 350)) else (if b.val < 123 then (if b.val < 119 then 299 else 321) else (if b.val < 127 then 347 else 0)))

def siblingMate116 (b : Fin 128) : Fin 408 :=
  (if b.val < 117 then (if b.val < 100 then (if b.val < 84 then 217 else 376) else (if b.val < 112 then 322 else 403)) else (if b.val < 124 then (if b.val < 118 then 315 else 401) else (if b.val < 127 then 373 else 23)))

def siblingMate117 (b : Fin 128) : Fin 408 :=
  (if b.val < 116 then (if b.val < 101 then (if b.val < 85 then 269 else 404) else (if b.val < 113 then 350 else 217)) else (if b.val < 125 then (if b.val < 119 then 317 else 385) else (if b.val < 127 then 272 else 142)))

def siblingMate118 (b : Fin 128) : Fin 408 :=
  (if b.val < 116 then (if b.val < 102 then (if b.val < 86 then 299 else 217) else (if b.val < 114 then 368 else 269)) else (if b.val < 126 then (if b.val < 119 then 404 else 298) else (if b.val < 127 then 369 else 47)))

def siblingMate119 (b : Fin 128) : Fin 408 :=
  (if b.val < 115 then (if b.val < 87 then 371 else (if b.val < 103 then 267 else 341)) else (if b.val < 118 then (if b.val < 117 then 323 else 405) else (if b.val < 127 then 297 else 305)))

def siblingMate120 (b : Fin 128) : Fin 408 :=
  (if b.val < 121 then (if b.val < 104 then (if b.val < 88 then 322 else 270) else (if b.val < 112 then 403 else 344)) else (if b.val < 124 then (if b.val < 122 then 351 else 217) else (if b.val < 127 then 315 else 273)))

def siblingMate121 (b : Fin 128) : Fin 408 :=
  (if b.val < 120 then (if b.val < 105 then (if b.val < 89 then 299 else 217) else (if b.val < 113 then 368 else 317)) else (if b.val < 125 then (if b.val < 123 then 350 else 321) else (if b.val < 127 then 347 else 46)))

def siblingMate122 (b : Fin 128) : Fin 408 :=
  (if b.val < 120 then (if b.val < 106 then (if b.val < 90 then 317 else 269) else (if b.val < 114 then 404 else 350)) else (if b.val < 126 then (if b.val < 123 then 217 else 385) else (if b.val < 127 then 272 else 175)))

def siblingMate123 (b : Fin 128) : Fin 408 :=
  (if b.val < 115 then (if b.val < 91 then 297 else (if b.val < 107 then 371 else 267)) else (if b.val < 122 then (if b.val < 121 then 341 else 323) else (if b.val < 127 then 405 else 279)))

def siblingMate124 (b : Fin 128) : Fin 408 :=
  (if b.val < 120 then (if b.val < 108 then (if b.val < 92 then 350 else 299) else (if b.val < 116 then 217 else 368)) else (if b.val < 126 then (if b.val < 125 then 317 else 321) else (if b.val < 127 then 347 else 76)))

def siblingMate125 (b : Fin 128) : Fin 408 :=
  (if b.val < 117 then (if b.val < 93 then 405 else (if b.val < 109 then 297 else 371)) else (if b.val < 124 then (if b.val < 121 then 267 else 341) else (if b.val < 127 then 323 else 253)))

def siblingMate126 (b : Fin 128) : Fin 408 :=
  (if b.val < 118 then (if b.val < 94 then 323 else (if b.val < 110 then 405 else 297)) else (if b.val < 124 then (if b.val < 122 then 371 else 267) else (if b.val < 127 then 341 else 224)))

def siblingMate127 (b : Fin 128) : Fin 408 :=
  (if b.val < 63 then (if b.val < 31 then (if b.val < 15 then (if b.val < 7 then (if b.val < 3 then (if b.val < 1 then 238 else (if b.val < 2 then 215 else 264)) else (if b.val < 5 then (if b.val < 4 then 107 else 292) else (if b.val < 6 then 22 else 283))) else (if b.val < 11 then (if b.val < 9 then (if b.val < 8 then 172 else 319) else (if b.val < 10 then 154 else 362)) else (if b.val < 13 then (if b.val < 12 then 2 else 274) else (if b.val < 14 then 82 else 288)))) else (if b.val < 23 then (if b.val < 19 then (if b.val < 17 then (if b.val < 16 then 131 else 348) else (if b.val < 18 then 61 else 258)) else (if b.val < 21 then (if b.val < 20 then 79 else 353) else (if b.val < 22 then 144 else 218))) else (if b.val < 27 then (if b.val < 25 then (if b.val < 24 then 200 else 236) else (if b.val < 26 then 212 else 367)) else (if b.val < 29 then (if b.val < 28 then 44 else 316) else (if b.val < 30 then 122 else 255))))) else (if b.val < 47 then (if b.val < 39 then (if b.val < 35 then (if b.val < 33 then (if b.val < 32 then 137 else 374) else (if b.val < 34 then 185 else 337)) else (if b.val < 37 then (if b.val < 36 then 140 else 234) else (if b.val < 38 then 210 else 366))) else (if b.val < 43 then (if b.val < 41 then (if b.val < 40 then 40 else 329) else (if b.val < 42 then 54 else 314)) else (if b.val < 45 then (if b.val < 44 then 106 else 266) else (if b.val < 46 then 183 else 389)))) else (if b.val < 55 then (if b.val < 51 then (if b.val < 49 then (if b.val < 48 then 45 else 398) else (if b.val < 50 then 117 else 263)) else (if b.val < 53 then (if b.val < 52 then 168 else 400) else (if b.val < 54 then 21 else 334))) else (if b.val < 59 then (if b.val < 57 then (if b.val < 56 then 170 else 345) else (if b.val < 58 then 90 else 284)) else (if b.val < 61 then (if b.val < 60 then 77 else 232) else (if b.val < 62 then 208 else 311)))))) else (if b.val < 95 then (if b.val < 79 then (if b.val < 71 then (if b.val < 67 then (if b.val < 65 then (if b.val < 64 then 157 else 406) else (if b.val < 66 then 92 else 230)) else (if b.val < 69 then (if b.val < 68 then 190 else 327) else (if b.val < 70 then 51 else 313))) else (if b.val < 75 then (if b.val < 73 then (if b.val < 72 then 103 else 397) else (if b.val < 74 then 116 else 262)) else (if b.val < 77 then (if b.val < 76 then 167 else 399) else (if b.val < 78 then 20 else 333)))) else (if b.val < 87 then (if b.val < 83 then (if b.val < 81 then (if b.val < 80 then 169 else 303) else (if b.val < 82 then 178 else 384)) else (if b.val < 85 then (if b.val < 84 then 16 else 343) else (if b.val < 86 then 89 else 281))) else (if b.val < 91 then (if b.val < 89 then (if b.val < 88 then 75 else 294) else (if b.val < 90 then 152 else 228)) else (if b.val < 93 then (if b.val < 92 then 188 else 378) else (if b.val < 94 then 113 else 382))))) else (if b.val < 111 then (if b.val < 103 then (if b.val < 99 then (if b.val < 97 then (if b.val < 96 then 128 else 381) else (if b.val < 98 then 28 else 340)) else (if b.val < 101 then (if b.val < 100 then 74 else 291) else (if b.val < 102 then 151 else 226))) else (if b.val < 107 then (if b.val < 105 then (if b.val < 104 then 186 else 242) else (if b.val < 106 then 206 else 361)) else (if b.val < 109 then (if b.val < 108 then 110 else 325) else (if b.val < 110 then 25 else 287)))) else (if b.val < 119 then (if b.val < 115 then (if b.val < 113 then (if b.val < 112 then 99 else 372) else (if b.val < 114 then 60 else 309)) else (if b.val < 117 then (if b.val < 116 then 3 else 275) else (if b.val < 118 then 143 else 364))) else (if b.val < 123 then (if b.val < 121 then (if b.val < 120 then 70 else 395) else (if b.val < 122 then 52 else 261)) else (if b.val < 125 then (if b.val < 124 then 43 else 342) else (if b.val < 126 then 19 else 223)))))))

def siblingMate (a b : Fin 128) : Fin 408 :=
  (if a.val < 64 then (if a.val < 32 then (if a.val < 16 then (if a.val < 8 then (if a.val < 4 then (if a.val < 2 then (if a.val < 1 then siblingMate0 b else siblingMate1 b) else (if a.val < 3 then siblingMate2 b else siblingMate3 b)) else (if a.val < 6 then (if a.val < 5 then siblingMate4 b else siblingMate5 b) else (if a.val < 7 then siblingMate6 b else siblingMate7 b))) else (if a.val < 12 then (if a.val < 10 then (if a.val < 9 then siblingMate8 b else siblingMate9 b) else (if a.val < 11 then siblingMate10 b else siblingMate11 b)) else (if a.val < 14 then (if a.val < 13 then siblingMate12 b else siblingMate13 b) else (if a.val < 15 then siblingMate14 b else siblingMate15 b)))) else (if a.val < 24 then (if a.val < 20 then (if a.val < 18 then (if a.val < 17 then siblingMate16 b else siblingMate17 b) else (if a.val < 19 then siblingMate18 b else siblingMate19 b)) else (if a.val < 22 then (if a.val < 21 then siblingMate20 b else siblingMate21 b) else (if a.val < 23 then siblingMate22 b else siblingMate23 b))) else (if a.val < 28 then (if a.val < 26 then (if a.val < 25 then siblingMate24 b else siblingMate25 b) else (if a.val < 27 then siblingMate26 b else siblingMate27 b)) else (if a.val < 30 then (if a.val < 29 then siblingMate28 b else siblingMate29 b) else (if a.val < 31 then siblingMate30 b else siblingMate31 b))))) else (if a.val < 48 then (if a.val < 40 then (if a.val < 36 then (if a.val < 34 then (if a.val < 33 then siblingMate32 b else siblingMate33 b) else (if a.val < 35 then siblingMate34 b else siblingMate35 b)) else (if a.val < 38 then (if a.val < 37 then siblingMate36 b else siblingMate37 b) else (if a.val < 39 then siblingMate38 b else siblingMate39 b))) else (if a.val < 44 then (if a.val < 42 then (if a.val < 41 then siblingMate40 b else siblingMate41 b) else (if a.val < 43 then siblingMate42 b else siblingMate43 b)) else (if a.val < 46 then (if a.val < 45 then siblingMate44 b else siblingMate45 b) else (if a.val < 47 then siblingMate46 b else siblingMate47 b)))) else (if a.val < 56 then (if a.val < 52 then (if a.val < 50 then (if a.val < 49 then siblingMate48 b else siblingMate49 b) else (if a.val < 51 then siblingMate50 b else siblingMate51 b)) else (if a.val < 54 then (if a.val < 53 then siblingMate52 b else siblingMate53 b) else (if a.val < 55 then siblingMate54 b else siblingMate55 b))) else (if a.val < 60 then (if a.val < 58 then (if a.val < 57 then siblingMate56 b else siblingMate57 b) else (if a.val < 59 then siblingMate58 b else siblingMate59 b)) else (if a.val < 62 then (if a.val < 61 then siblingMate60 b else siblingMate61 b) else (if a.val < 63 then siblingMate62 b else siblingMate63 b)))))) else (if a.val < 96 then (if a.val < 80 then (if a.val < 72 then (if a.val < 68 then (if a.val < 66 then (if a.val < 65 then siblingMate64 b else siblingMate65 b) else (if a.val < 67 then siblingMate66 b else siblingMate67 b)) else (if a.val < 70 then (if a.val < 69 then siblingMate68 b else siblingMate69 b) else (if a.val < 71 then siblingMate70 b else siblingMate71 b))) else (if a.val < 76 then (if a.val < 74 then (if a.val < 73 then siblingMate72 b else siblingMate73 b) else (if a.val < 75 then siblingMate74 b else siblingMate75 b)) else (if a.val < 78 then (if a.val < 77 then siblingMate76 b else siblingMate77 b) else (if a.val < 79 then siblingMate78 b else siblingMate79 b)))) else (if a.val < 88 then (if a.val < 84 then (if a.val < 82 then (if a.val < 81 then siblingMate80 b else siblingMate81 b) else (if a.val < 83 then siblingMate82 b else siblingMate83 b)) else (if a.val < 86 then (if a.val < 85 then siblingMate84 b else siblingMate85 b) else (if a.val < 87 then siblingMate86 b else siblingMate87 b))) else (if a.val < 92 then (if a.val < 90 then (if a.val < 89 then siblingMate88 b else siblingMate89 b) else (if a.val < 91 then siblingMate90 b else siblingMate91 b)) else (if a.val < 94 then (if a.val < 93 then siblingMate92 b else siblingMate93 b) else (if a.val < 95 then siblingMate94 b else siblingMate95 b))))) else (if a.val < 112 then (if a.val < 104 then (if a.val < 100 then (if a.val < 98 then (if a.val < 97 then siblingMate96 b else siblingMate97 b) else (if a.val < 99 then siblingMate98 b else siblingMate99 b)) else (if a.val < 102 then (if a.val < 101 then siblingMate100 b else siblingMate101 b) else (if a.val < 103 then siblingMate102 b else siblingMate103 b))) else (if a.val < 108 then (if a.val < 106 then (if a.val < 105 then siblingMate104 b else siblingMate105 b) else (if a.val < 107 then siblingMate106 b else siblingMate107 b)) else (if a.val < 110 then (if a.val < 109 then siblingMate108 b else siblingMate109 b) else (if a.val < 111 then siblingMate110 b else siblingMate111 b)))) else (if a.val < 120 then (if a.val < 116 then (if a.val < 114 then (if a.val < 113 then siblingMate112 b else siblingMate113 b) else (if a.val < 115 then siblingMate114 b else siblingMate115 b)) else (if a.val < 118 then (if a.val < 117 then siblingMate116 b else siblingMate117 b) else (if a.val < 119 then siblingMate118 b else siblingMate119 b))) else (if a.val < 124 then (if a.val < 122 then (if a.val < 121 then siblingMate120 b else siblingMate121 b) else (if a.val < 123 then siblingMate122 b else siblingMate123 b)) else (if a.val < 126 then (if a.val < 125 then siblingMate124 b else siblingMate125 b) else (if a.val < 127 then siblingMate126 b else siblingMate127 b)))))))

end SparseMonotiles.CarrierHierarchy.T7SiblingData
