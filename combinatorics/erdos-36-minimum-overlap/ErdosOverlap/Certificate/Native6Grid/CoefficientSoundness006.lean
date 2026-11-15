/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck048
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck049
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck050
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck051
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck052
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck053
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck054
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck055

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk006 (j : ℕ) (hlo : 384 ≤ j) (hhi : j < 448) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0384
  · exact coefficientCheck0385
  · exact coefficientCheck0386
  · exact coefficientCheck0387
  · exact coefficientCheck0388
  · exact coefficientCheck0389
  · exact coefficientCheck0390
  · exact coefficientCheck0391
  · exact coefficientCheck0392
  · exact coefficientCheck0393
  · exact coefficientCheck0394
  · exact coefficientCheck0395
  · exact coefficientCheck0396
  · exact coefficientCheck0397
  · exact coefficientCheck0398
  · exact coefficientCheck0399
  · exact coefficientCheck0400
  · exact coefficientCheck0401
  · exact coefficientCheck0402
  · exact coefficientCheck0403
  · exact coefficientCheck0404
  · exact coefficientCheck0405
  · exact coefficientCheck0406
  · exact coefficientCheck0407
  · exact coefficientCheck0408
  · exact coefficientCheck0409
  · exact coefficientCheck0410
  · exact coefficientCheck0411
  · exact coefficientCheck0412
  · exact coefficientCheck0413
  · exact coefficientCheck0414
  · exact coefficientCheck0415
  · exact coefficientCheck0416
  · exact coefficientCheck0417
  · exact coefficientCheck0418
  · exact coefficientCheck0419
  · exact coefficientCheck0420
  · exact coefficientCheck0421
  · exact coefficientCheck0422
  · exact coefficientCheck0423
  · exact coefficientCheck0424
  · exact coefficientCheck0425
  · exact coefficientCheck0426
  · exact coefficientCheck0427
  · exact coefficientCheck0428
  · exact coefficientCheck0429
  · exact coefficientCheck0430
  · exact coefficientCheck0431
  · exact coefficientCheck0432
  · exact coefficientCheck0433
  · exact coefficientCheck0434
  · exact coefficientCheck0435
  · exact coefficientCheck0436
  · exact coefficientCheck0437
  · exact coefficientCheck0438
  · exact coefficientCheck0439
  · exact coefficientCheck0440
  · exact coefficientCheck0441
  · exact coefficientCheck0442
  · exact coefficientCheck0443
  · exact coefficientCheck0444
  · exact coefficientCheck0445
  · exact coefficientCheck0446
  · exact coefficientCheck0447

end
end ErdosOverlap.Native6Grid
