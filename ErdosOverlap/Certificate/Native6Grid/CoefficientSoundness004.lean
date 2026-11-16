/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Grid.Rows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientRows
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck032
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck033
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck034
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck035
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck036
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck037
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck038
public import ErdosOverlap.Certificate.Native6Grid.CoefficientCheck039

namespace ErdosOverlap.Native6Grid

open Numerics

public section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficients_chunk004 (j : ℕ) (hlo : 256 ≤ j) (hhi : j < 320) :
    completeCoefficientRowCheck factorRow (stateRow j) j (coefficientRow j) = true := by
  interval_cases j
  · exact coefficientCheck0256
  · exact coefficientCheck0257
  · exact coefficientCheck0258
  · exact coefficientCheck0259
  · exact coefficientCheck0260
  · exact coefficientCheck0261
  · exact coefficientCheck0262
  · exact coefficientCheck0263
  · exact coefficientCheck0264
  · exact coefficientCheck0265
  · exact coefficientCheck0266
  · exact coefficientCheck0267
  · exact coefficientCheck0268
  · exact coefficientCheck0269
  · exact coefficientCheck0270
  · exact coefficientCheck0271
  · exact coefficientCheck0272
  · exact coefficientCheck0273
  · exact coefficientCheck0274
  · exact coefficientCheck0275
  · exact coefficientCheck0276
  · exact coefficientCheck0277
  · exact coefficientCheck0278
  · exact coefficientCheck0279
  · exact coefficientCheck0280
  · exact coefficientCheck0281
  · exact coefficientCheck0282
  · exact coefficientCheck0283
  · exact coefficientCheck0284
  · exact coefficientCheck0285
  · exact coefficientCheck0286
  · exact coefficientCheck0287
  · exact coefficientCheck0288
  · exact coefficientCheck0289
  · exact coefficientCheck0290
  · exact coefficientCheck0291
  · exact coefficientCheck0292
  · exact coefficientCheck0293
  · exact coefficientCheck0294
  · exact coefficientCheck0295
  · exact coefficientCheck0296
  · exact coefficientCheck0297
  · exact coefficientCheck0298
  · exact coefficientCheck0299
  · exact coefficientCheck0300
  · exact coefficientCheck0301
  · exact coefficientCheck0302
  · exact coefficientCheck0303
  · exact coefficientCheck0304
  · exact coefficientCheck0305
  · exact coefficientCheck0306
  · exact coefficientCheck0307
  · exact coefficientCheck0308
  · exact coefficientCheck0309
  · exact coefficientCheck0310
  · exact coefficientCheck0311
  · exact coefficientCheck0312
  · exact coefficientCheck0313
  · exact coefficientCheck0314
  · exact coefficientCheck0315
  · exact coefficientCheck0316
  · exact coefficientCheck0317
  · exact coefficientCheck0318
  · exact coefficientCheck0319

end
end ErdosOverlap.Native6Grid
