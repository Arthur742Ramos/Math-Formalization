/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck040
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck041
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck042
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck043
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck044
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck045
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck046
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck047

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk005 (j : ℕ) (hlo : 320 ≤ j) (hhi : j < 384) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0320
  · exact coefficientCheck0321
  · exact coefficientCheck0322
  · exact coefficientCheck0323
  · exact coefficientCheck0324
  · exact coefficientCheck0325
  · exact coefficientCheck0326
  · exact coefficientCheck0327
  · exact coefficientCheck0328
  · exact coefficientCheck0329
  · exact coefficientCheck0330
  · exact coefficientCheck0331
  · exact coefficientCheck0332
  · exact coefficientCheck0333
  · exact coefficientCheck0334
  · exact coefficientCheck0335
  · exact coefficientCheck0336
  · exact coefficientCheck0337
  · exact coefficientCheck0338
  · exact coefficientCheck0339
  · exact coefficientCheck0340
  · exact coefficientCheck0341
  · exact coefficientCheck0342
  · exact coefficientCheck0343
  · exact coefficientCheck0344
  · exact coefficientCheck0345
  · exact coefficientCheck0346
  · exact coefficientCheck0347
  · exact coefficientCheck0348
  · exact coefficientCheck0349
  · exact coefficientCheck0350
  · exact coefficientCheck0351
  · exact coefficientCheck0352
  · exact coefficientCheck0353
  · exact coefficientCheck0354
  · exact coefficientCheck0355
  · exact coefficientCheck0356
  · exact coefficientCheck0357
  · exact coefficientCheck0358
  · exact coefficientCheck0359
  · exact coefficientCheck0360
  · exact coefficientCheck0361
  · exact coefficientCheck0362
  · exact coefficientCheck0363
  · exact coefficientCheck0364
  · exact coefficientCheck0365
  · exact coefficientCheck0366
  · exact coefficientCheck0367
  · exact coefficientCheck0368
  · exact coefficientCheck0369
  · exact coefficientCheck0370
  · exact coefficientCheck0371
  · exact coefficientCheck0372
  · exact coefficientCheck0373
  · exact coefficientCheck0374
  · exact coefficientCheck0375
  · exact coefficientCheck0376
  · exact coefficientCheck0377
  · exact coefficientCheck0378
  · exact coefficientCheck0379
  · exact coefficientCheck0380
  · exact coefficientCheck0381
  · exact coefficientCheck0382
  · exact coefficientCheck0383

end
end ErdosOverlap.Native6Grid
