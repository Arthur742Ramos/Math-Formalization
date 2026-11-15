/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6Leaves.GeometryData0002
public import ErdosOverlap.Certificate.Native6Leaves.GeometryData0003
public import ErdosOverlap.Certificate.Native6Leaves.GeometryTraceData0001
public import ErdosOverlap.Certificate.Native6Leaves.PatchCheck0003
public import ErdosOverlap.Certificate.Native6Leaves.PatchCheck0004
public import ErdosOverlap.Certificate.Native6Leaves.PatchCheck0005
public import ErdosOverlap.Certificate.Native6Leaves.PatchCheck0006
public import ErdosOverlap.Numerics.NativePolynomialDirectTrace

namespace ErdosOverlap.Native6Leaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def checkedGeometry00256 : CheckedGeometry :=
  ⟨geometry00256, Geometry.check_of_directTraceCheck geometry00256
    checkedPatchCache0250 checkedPatchCache0251
    geometryTraceA00256 geometryTraceB00256 (by decide +kernel)⟩

def checkedGeometry00257 : CheckedGeometry :=
  ⟨geometry00257, Geometry.check_of_directTraceCheck geometry00257
    checkedPatchCache0250 checkedPatchCache0251
    geometryTraceA00257 geometryTraceB00257 (by decide +kernel)⟩

def checkedGeometry00258 : CheckedGeometry :=
  ⟨geometry00258, Geometry.check_of_directTraceCheck geometry00258
    checkedPatchCache0250 checkedPatchCache0251
    geometryTraceA00258 geometryTraceB00258 (by decide +kernel)⟩

def checkedGeometry00259 : CheckedGeometry :=
  ⟨geometry00259, Geometry.check_of_directTraceCheck geometry00259
    checkedPatchCache0250 checkedPatchCache0251
    geometryTraceA00259 geometryTraceB00259 (by decide +kernel)⟩

def checkedGeometry00260 : CheckedGeometry :=
  ⟨geometry00260, Geometry.check_of_directTraceCheck geometry00260
    checkedPatchCache0252 checkedPatchCache0253
    geometryTraceA00260 geometryTraceB00260 (by decide +kernel)⟩

def checkedGeometry00261 : CheckedGeometry :=
  ⟨geometry00261, Geometry.check_of_directTraceCheck geometry00261
    checkedPatchCache0252 checkedPatchCache0253
    geometryTraceA00261 geometryTraceB00261 (by decide +kernel)⟩

def checkedGeometry00262 : CheckedGeometry :=
  ⟨geometry00262, Geometry.check_of_directTraceCheck geometry00262
    checkedPatchCache0252 checkedPatchCache0253
    geometryTraceA00262 geometryTraceB00262 (by decide +kernel)⟩

def checkedGeometry00263 : CheckedGeometry :=
  ⟨geometry00263, Geometry.check_of_directTraceCheck geometry00263
    checkedPatchCache0252 checkedPatchCache0253
    geometryTraceA00263 geometryTraceB00263 (by decide +kernel)⟩

def checkedGeometry00264 : CheckedGeometry :=
  ⟨geometry00264, Geometry.check_of_directTraceCheck geometry00264
    checkedPatchCache0252 checkedPatchCache0253
    geometryTraceA00264 geometryTraceB00264 (by decide +kernel)⟩

def checkedGeometry00265 : CheckedGeometry :=
  ⟨geometry00265, Geometry.check_of_directTraceCheck geometry00265
    checkedPatchCache0252 checkedPatchCache0253
    geometryTraceA00265 geometryTraceB00265 (by decide +kernel)⟩

def checkedGeometry00266 : CheckedGeometry :=
  ⟨geometry00266, Geometry.check_of_directTraceCheck geometry00266
    checkedPatchCache0252 checkedPatchCache0253
    geometryTraceA00266 geometryTraceB00266 (by decide +kernel)⟩

def checkedGeometry00267 : CheckedGeometry :=
  ⟨geometry00267, Geometry.check_of_directTraceCheck geometry00267
    checkedPatchCache0252 checkedPatchCache0253
    geometryTraceA00267 geometryTraceB00267 (by decide +kernel)⟩

def checkedGeometry00268 : CheckedGeometry :=
  ⟨geometry00268, Geometry.check_of_directTraceCheck geometry00268
    checkedPatchCache0252 checkedPatchCache0253
    geometryTraceA00268 geometryTraceB00268 (by decide +kernel)⟩

def checkedGeometry00269 : CheckedGeometry :=
  ⟨geometry00269, Geometry.check_of_directTraceCheck geometry00269
    checkedPatchCache0254 checkedPatchCache0255
    geometryTraceA00269 geometryTraceB00269 (by decide +kernel)⟩

def checkedGeometry00270 : CheckedGeometry :=
  ⟨geometry00270, Geometry.check_of_directTraceCheck geometry00270
    checkedPatchCache0254 checkedPatchCache0255
    geometryTraceA00270 geometryTraceB00270 (by decide +kernel)⟩

def checkedGeometry00271 : CheckedGeometry :=
  ⟨geometry00271, Geometry.check_of_directTraceCheck geometry00271
    checkedPatchCache0254 checkedPatchCache0255
    geometryTraceA00271 geometryTraceB00271 (by decide +kernel)⟩

def checkedGeometry00272 : CheckedGeometry :=
  ⟨geometry00272, Geometry.check_of_directTraceCheck geometry00272
    checkedPatchCache0254 checkedPatchCache0255
    geometryTraceA00272 geometryTraceB00272 (by decide +kernel)⟩

def checkedGeometry00273 : CheckedGeometry :=
  ⟨geometry00273, Geometry.check_of_directTraceCheck geometry00273
    checkedPatchCache0254 checkedPatchCache0255
    geometryTraceA00273 geometryTraceB00273 (by decide +kernel)⟩

def checkedGeometry00274 : CheckedGeometry :=
  ⟨geometry00274, Geometry.check_of_directTraceCheck geometry00274
    checkedPatchCache0254 checkedPatchCache0255
    geometryTraceA00274 geometryTraceB00274 (by decide +kernel)⟩

def checkedGeometry00275 : CheckedGeometry :=
  ⟨geometry00275, Geometry.check_of_directTraceCheck geometry00275
    checkedPatchCache0254 checkedPatchCache0255
    geometryTraceA00275 geometryTraceB00275 (by decide +kernel)⟩

def checkedGeometry00276 : CheckedGeometry :=
  ⟨geometry00276, Geometry.check_of_directTraceCheck geometry00276
    checkedPatchCache0254 checkedPatchCache0255
    geometryTraceA00276 geometryTraceB00276 (by decide +kernel)⟩

def checkedGeometry00277 : CheckedGeometry :=
  ⟨geometry00277, Geometry.check_of_directTraceCheck geometry00277
    checkedPatchCache0256 checkedPatchCache0257
    geometryTraceA00277 geometryTraceB00277 (by decide +kernel)⟩

def checkedGeometry00278 : CheckedGeometry :=
  ⟨geometry00278, Geometry.check_of_directTraceCheck geometry00278
    checkedPatchCache0258 checkedPatchCache0259
    geometryTraceA00278 geometryTraceB00278 (by decide +kernel)⟩

def checkedGeometry00279 : CheckedGeometry :=
  ⟨geometry00279, Geometry.check_of_directTraceCheck geometry00279
    checkedPatchCache0260 checkedPatchCache0261
    geometryTraceA00279 geometryTraceB00279 (by decide +kernel)⟩

def checkedGeometry00280 : CheckedGeometry :=
  ⟨geometry00280, Geometry.check_of_directTraceCheck geometry00280
    checkedPatchCache0262 checkedPatchCache0263
    geometryTraceA00280 geometryTraceB00280 (by decide +kernel)⟩

def checkedGeometry00281 : CheckedGeometry :=
  ⟨geometry00281, Geometry.check_of_directTraceCheck geometry00281
    checkedPatchCache0264 checkedPatchCache0265
    geometryTraceA00281 geometryTraceB00281 (by decide +kernel)⟩

def checkedGeometry00282 : CheckedGeometry :=
  ⟨geometry00282, Geometry.check_of_directTraceCheck geometry00282
    checkedPatchCache0266 checkedPatchCache0267
    geometryTraceA00282 geometryTraceB00282 (by decide +kernel)⟩

def checkedGeometry00283 : CheckedGeometry :=
  ⟨geometry00283, Geometry.check_of_directTraceCheck geometry00283
    checkedPatchCache0268 checkedPatchCache0269
    geometryTraceA00283 geometryTraceB00283 (by decide +kernel)⟩

def checkedGeometry00284 : CheckedGeometry :=
  ⟨geometry00284, Geometry.check_of_directTraceCheck geometry00284
    checkedPatchCache0270 checkedPatchCache0271
    geometryTraceA00284 geometryTraceB00284 (by decide +kernel)⟩

def checkedGeometry00285 : CheckedGeometry :=
  ⟨geometry00285, Geometry.check_of_directTraceCheck geometry00285
    checkedPatchCache0272 checkedPatchCache0273
    geometryTraceA00285 geometryTraceB00285 (by decide +kernel)⟩

def checkedGeometry00286 : CheckedGeometry :=
  ⟨geometry00286, Geometry.check_of_directTraceCheck geometry00286
    checkedPatchCache0274 checkedPatchCache0275
    geometryTraceA00286 geometryTraceB00286 (by decide +kernel)⟩

def checkedGeometry00287 : CheckedGeometry :=
  ⟨geometry00287, Geometry.check_of_directTraceCheck geometry00287
    checkedPatchCache0276 checkedPatchCache0277
    geometryTraceA00287 geometryTraceB00287 (by decide +kernel)⟩

def checkedGeometry00288 : CheckedGeometry :=
  ⟨geometry00288, Geometry.check_of_directTraceCheck geometry00288
    checkedPatchCache0278 checkedPatchCache0279
    geometryTraceA00288 geometryTraceB00288 (by decide +kernel)⟩

def checkedGeometry00289 : CheckedGeometry :=
  ⟨geometry00289, Geometry.check_of_directTraceCheck geometry00289
    checkedPatchCache0280 checkedPatchCache0281
    geometryTraceA00289 geometryTraceB00289 (by decide +kernel)⟩

def checkedGeometry00290 : CheckedGeometry :=
  ⟨geometry00290, Geometry.check_of_directTraceCheck geometry00290
    checkedPatchCache0282 checkedPatchCache0283
    geometryTraceA00290 geometryTraceB00290 (by decide +kernel)⟩

def checkedGeometry00291 : CheckedGeometry :=
  ⟨geometry00291, Geometry.check_of_directTraceCheck geometry00291
    checkedPatchCache0284 checkedPatchCache0285
    geometryTraceA00291 geometryTraceB00291 (by decide +kernel)⟩

def checkedGeometry00292 : CheckedGeometry :=
  ⟨geometry00292, Geometry.check_of_directTraceCheck geometry00292
    checkedPatchCache0286 checkedPatchCache0287
    geometryTraceA00292 geometryTraceB00292 (by decide +kernel)⟩

def checkedGeometry00293 : CheckedGeometry :=
  ⟨geometry00293, Geometry.check_of_directTraceCheck geometry00293
    checkedPatchCache0288 checkedPatchCache0289
    geometryTraceA00293 geometryTraceB00293 (by decide +kernel)⟩

def checkedGeometry00294 : CheckedGeometry :=
  ⟨geometry00294, Geometry.check_of_directTraceCheck geometry00294
    checkedPatchCache0290 checkedPatchCache0291
    geometryTraceA00294 geometryTraceB00294 (by decide +kernel)⟩

def checkedGeometry00295 : CheckedGeometry :=
  ⟨geometry00295, Geometry.check_of_directTraceCheck geometry00295
    checkedPatchCache0292 checkedPatchCache0293
    geometryTraceA00295 geometryTraceB00295 (by decide +kernel)⟩

def checkedGeometry00296 : CheckedGeometry :=
  ⟨geometry00296, Geometry.check_of_directTraceCheck geometry00296
    checkedPatchCache0294 checkedPatchCache0295
    geometryTraceA00296 geometryTraceB00296 (by decide +kernel)⟩

def checkedGeometry00297 : CheckedGeometry :=
  ⟨geometry00297, Geometry.check_of_directTraceCheck geometry00297
    checkedPatchCache0296 checkedPatchCache0297
    geometryTraceA00297 geometryTraceB00297 (by decide +kernel)⟩

def checkedGeometry00298 : CheckedGeometry :=
  ⟨geometry00298, Geometry.check_of_directTraceCheck geometry00298
    checkedPatchCache0298 checkedPatchCache0299
    geometryTraceA00298 geometryTraceB00298 (by decide +kernel)⟩

def checkedGeometry00299 : CheckedGeometry :=
  ⟨geometry00299, Geometry.check_of_directTraceCheck geometry00299
    checkedPatchCache0300 checkedPatchCache0301
    geometryTraceA00299 geometryTraceB00299 (by decide +kernel)⟩

def checkedGeometry00300 : CheckedGeometry :=
  ⟨geometry00300, Geometry.check_of_directTraceCheck geometry00300
    checkedPatchCache0302 checkedPatchCache0303
    geometryTraceA00300 geometryTraceB00300 (by decide +kernel)⟩

def checkedGeometry00301 : CheckedGeometry :=
  ⟨geometry00301, Geometry.check_of_directTraceCheck geometry00301
    checkedPatchCache0304 checkedPatchCache0305
    geometryTraceA00301 geometryTraceB00301 (by decide +kernel)⟩

def checkedGeometry00302 : CheckedGeometry :=
  ⟨geometry00302, Geometry.check_of_directTraceCheck geometry00302
    checkedPatchCache0306 checkedPatchCache0307
    geometryTraceA00302 geometryTraceB00302 (by decide +kernel)⟩

def checkedGeometry00303 : CheckedGeometry :=
  ⟨geometry00303, Geometry.check_of_directTraceCheck geometry00303
    checkedPatchCache0308 checkedPatchCache0309
    geometryTraceA00303 geometryTraceB00303 (by decide +kernel)⟩

def checkedGeometry00304 : CheckedGeometry :=
  ⟨geometry00304, Geometry.check_of_directTraceCheck geometry00304
    checkedPatchCache0310 checkedPatchCache0311
    geometryTraceA00304 geometryTraceB00304 (by decide +kernel)⟩

def checkedGeometry00305 : CheckedGeometry :=
  ⟨geometry00305, Geometry.check_of_directTraceCheck geometry00305
    checkedPatchCache0312 checkedPatchCache0313
    geometryTraceA00305 geometryTraceB00305 (by decide +kernel)⟩

def checkedGeometry00306 : CheckedGeometry :=
  ⟨geometry00306, Geometry.check_of_directTraceCheck geometry00306
    checkedPatchCache0314 checkedPatchCache0315
    geometryTraceA00306 geometryTraceB00306 (by decide +kernel)⟩

def checkedGeometry00307 : CheckedGeometry :=
  ⟨geometry00307, Geometry.check_of_directTraceCheck geometry00307
    checkedPatchCache0316 checkedPatchCache0317
    geometryTraceA00307 geometryTraceB00307 (by decide +kernel)⟩

def checkedGeometry00308 : CheckedGeometry :=
  ⟨geometry00308, Geometry.check_of_directTraceCheck geometry00308
    checkedPatchCache0318 checkedPatchCache0319
    geometryTraceA00308 geometryTraceB00308 (by decide +kernel)⟩

def checkedGeometry00309 : CheckedGeometry :=
  ⟨geometry00309, Geometry.check_of_directTraceCheck geometry00309
    checkedPatchCache0320 checkedPatchCache0321
    geometryTraceA00309 geometryTraceB00309 (by decide +kernel)⟩

def checkedGeometry00310 : CheckedGeometry :=
  ⟨geometry00310, Geometry.check_of_directTraceCheck geometry00310
    checkedPatchCache0322 checkedPatchCache0323
    geometryTraceA00310 geometryTraceB00310 (by decide +kernel)⟩

def checkedGeometry00311 : CheckedGeometry :=
  ⟨geometry00311, Geometry.check_of_directTraceCheck geometry00311
    checkedPatchCache0324 checkedPatchCache0325
    geometryTraceA00311 geometryTraceB00311 (by decide +kernel)⟩

def checkedGeometry00312 : CheckedGeometry :=
  ⟨geometry00312, Geometry.check_of_directTraceCheck geometry00312
    checkedPatchCache0326 checkedPatchCache0327
    geometryTraceA00312 geometryTraceB00312 (by decide +kernel)⟩

def checkedGeometry00313 : CheckedGeometry :=
  ⟨geometry00313, Geometry.check_of_directTraceCheck geometry00313
    checkedPatchCache0328 checkedPatchCache0329
    geometryTraceA00313 geometryTraceB00313 (by decide +kernel)⟩

def checkedGeometry00314 : CheckedGeometry :=
  ⟨geometry00314, Geometry.check_of_directTraceCheck geometry00314
    checkedPatchCache0330 checkedPatchCache0331
    geometryTraceA00314 geometryTraceB00314 (by decide +kernel)⟩

def checkedGeometry00315 : CheckedGeometry :=
  ⟨geometry00315, Geometry.check_of_directTraceCheck geometry00315
    checkedPatchCache0332 checkedPatchCache0333
    geometryTraceA00315 geometryTraceB00315 (by decide +kernel)⟩

def checkedGeometry00316 : CheckedGeometry :=
  ⟨geometry00316, Geometry.check_of_directTraceCheck geometry00316
    checkedPatchCache0334 checkedPatchCache0335
    geometryTraceA00316 geometryTraceB00316 (by decide +kernel)⟩

def checkedGeometry00317 : CheckedGeometry :=
  ⟨geometry00317, Geometry.check_of_directTraceCheck geometry00317
    checkedPatchCache0336 checkedPatchCache0337
    geometryTraceA00317 geometryTraceB00317 (by decide +kernel)⟩

def checkedGeometry00318 : CheckedGeometry :=
  ⟨geometry00318, Geometry.check_of_directTraceCheck geometry00318
    checkedPatchCache0338 checkedPatchCache0339
    geometryTraceA00318 geometryTraceB00318 (by decide +kernel)⟩

def checkedGeometry00319 : CheckedGeometry :=
  ⟨geometry00319, Geometry.check_of_directTraceCheck geometry00319
    checkedPatchCache0338 checkedPatchCache0339
    geometryTraceA00319 geometryTraceB00319 (by decide +kernel)⟩

def checkedGeometry00320 : CheckedGeometry :=
  ⟨geometry00320, Geometry.check_of_directTraceCheck geometry00320
    checkedPatchCache0338 checkedPatchCache0339
    geometryTraceA00320 geometryTraceB00320 (by decide +kernel)⟩

def checkedGeometry00321 : CheckedGeometry :=
  ⟨geometry00321, Geometry.check_of_directTraceCheck geometry00321
    checkedPatchCache0338 checkedPatchCache0339
    geometryTraceA00321 geometryTraceB00321 (by decide +kernel)⟩

def checkedGeometry00322 : CheckedGeometry :=
  ⟨geometry00322, Geometry.check_of_directTraceCheck geometry00322
    checkedPatchCache0338 checkedPatchCache0339
    geometryTraceA00322 geometryTraceB00322 (by decide +kernel)⟩

def checkedGeometry00323 : CheckedGeometry :=
  ⟨geometry00323, Geometry.check_of_directTraceCheck geometry00323
    checkedPatchCache0338 checkedPatchCache0339
    geometryTraceA00323 geometryTraceB00323 (by decide +kernel)⟩

def checkedGeometry00324 : CheckedGeometry :=
  ⟨geometry00324, Geometry.check_of_directTraceCheck geometry00324
    checkedPatchCache0338 checkedPatchCache0339
    geometryTraceA00324 geometryTraceB00324 (by decide +kernel)⟩

def checkedGeometry00325 : CheckedGeometry :=
  ⟨geometry00325, Geometry.check_of_directTraceCheck geometry00325
    checkedPatchCache0340 checkedPatchCache0341
    geometryTraceA00325 geometryTraceB00325 (by decide +kernel)⟩

def checkedGeometry00326 : CheckedGeometry :=
  ⟨geometry00326, Geometry.check_of_directTraceCheck geometry00326
    checkedPatchCache0340 checkedPatchCache0341
    geometryTraceA00326 geometryTraceB00326 (by decide +kernel)⟩

def checkedGeometry00327 : CheckedGeometry :=
  ⟨geometry00327, Geometry.check_of_directTraceCheck geometry00327
    checkedPatchCache0340 checkedPatchCache0341
    geometryTraceA00327 geometryTraceB00327 (by decide +kernel)⟩

def checkedGeometry00328 : CheckedGeometry :=
  ⟨geometry00328, Geometry.check_of_directTraceCheck geometry00328
    checkedPatchCache0340 checkedPatchCache0341
    geometryTraceA00328 geometryTraceB00328 (by decide +kernel)⟩

def checkedGeometry00329 : CheckedGeometry :=
  ⟨geometry00329, Geometry.check_of_directTraceCheck geometry00329
    checkedPatchCache0340 checkedPatchCache0341
    geometryTraceA00329 geometryTraceB00329 (by decide +kernel)⟩

def checkedGeometry00330 : CheckedGeometry :=
  ⟨geometry00330, Geometry.check_of_directTraceCheck geometry00330
    checkedPatchCache0340 checkedPatchCache0341
    geometryTraceA00330 geometryTraceB00330 (by decide +kernel)⟩

def checkedGeometry00331 : CheckedGeometry :=
  ⟨geometry00331, Geometry.check_of_directTraceCheck geometry00331
    checkedPatchCache0340 checkedPatchCache0341
    geometryTraceA00331 geometryTraceB00331 (by decide +kernel)⟩

def checkedGeometry00332 : CheckedGeometry :=
  ⟨geometry00332, Geometry.check_of_directTraceCheck geometry00332
    checkedPatchCache0340 checkedPatchCache0341
    geometryTraceA00332 geometryTraceB00332 (by decide +kernel)⟩

def checkedGeometry00333 : CheckedGeometry :=
  ⟨geometry00333, Geometry.check_of_directTraceCheck geometry00333
    checkedPatchCache0342 checkedPatchCache0343
    geometryTraceA00333 geometryTraceB00333 (by decide +kernel)⟩

def checkedGeometry00334 : CheckedGeometry :=
  ⟨geometry00334, Geometry.check_of_directTraceCheck geometry00334
    checkedPatchCache0342 checkedPatchCache0343
    geometryTraceA00334 geometryTraceB00334 (by decide +kernel)⟩

def checkedGeometry00335 : CheckedGeometry :=
  ⟨geometry00335, Geometry.check_of_directTraceCheck geometry00335
    checkedPatchCache0342 checkedPatchCache0343
    geometryTraceA00335 geometryTraceB00335 (by decide +kernel)⟩

def checkedGeometry00336 : CheckedGeometry :=
  ⟨geometry00336, Geometry.check_of_directTraceCheck geometry00336
    checkedPatchCache0342 checkedPatchCache0343
    geometryTraceA00336 geometryTraceB00336 (by decide +kernel)⟩

def checkedGeometry00337 : CheckedGeometry :=
  ⟨geometry00337, Geometry.check_of_directTraceCheck geometry00337
    checkedPatchCache0342 checkedPatchCache0343
    geometryTraceA00337 geometryTraceB00337 (by decide +kernel)⟩

def checkedGeometry00338 : CheckedGeometry :=
  ⟨geometry00338, Geometry.check_of_directTraceCheck geometry00338
    checkedPatchCache0342 checkedPatchCache0343
    geometryTraceA00338 geometryTraceB00338 (by decide +kernel)⟩

def checkedGeometry00339 : CheckedGeometry :=
  ⟨geometry00339, Geometry.check_of_directTraceCheck geometry00339
    checkedPatchCache0342 checkedPatchCache0343
    geometryTraceA00339 geometryTraceB00339 (by decide +kernel)⟩

def checkedGeometry00340 : CheckedGeometry :=
  ⟨geometry00340, Geometry.check_of_directTraceCheck geometry00340
    checkedPatchCache0342 checkedPatchCache0343
    geometryTraceA00340 geometryTraceB00340 (by decide +kernel)⟩

def checkedGeometry00341 : CheckedGeometry :=
  ⟨geometry00341, Geometry.check_of_directTraceCheck geometry00341
    checkedPatchCache0344 checkedPatchCache0345
    geometryTraceA00341 geometryTraceB00341 (by decide +kernel)⟩

def checkedGeometry00342 : CheckedGeometry :=
  ⟨geometry00342, Geometry.check_of_directTraceCheck geometry00342
    checkedPatchCache0344 checkedPatchCache0345
    geometryTraceA00342 geometryTraceB00342 (by decide +kernel)⟩

def checkedGeometry00343 : CheckedGeometry :=
  ⟨geometry00343, Geometry.check_of_directTraceCheck geometry00343
    checkedPatchCache0344 checkedPatchCache0345
    geometryTraceA00343 geometryTraceB00343 (by decide +kernel)⟩

def checkedGeometry00344 : CheckedGeometry :=
  ⟨geometry00344, Geometry.check_of_directTraceCheck geometry00344
    checkedPatchCache0344 checkedPatchCache0345
    geometryTraceA00344 geometryTraceB00344 (by decide +kernel)⟩

def checkedGeometry00345 : CheckedGeometry :=
  ⟨geometry00345, Geometry.check_of_directTraceCheck geometry00345
    checkedPatchCache0344 checkedPatchCache0345
    geometryTraceA00345 geometryTraceB00345 (by decide +kernel)⟩

def checkedGeometry00346 : CheckedGeometry :=
  ⟨geometry00346, Geometry.check_of_directTraceCheck geometry00346
    checkedPatchCache0344 checkedPatchCache0345
    geometryTraceA00346 geometryTraceB00346 (by decide +kernel)⟩

def checkedGeometry00347 : CheckedGeometry :=
  ⟨geometry00347, Geometry.check_of_directTraceCheck geometry00347
    checkedPatchCache0344 checkedPatchCache0345
    geometryTraceA00347 geometryTraceB00347 (by decide +kernel)⟩

def checkedGeometry00348 : CheckedGeometry :=
  ⟨geometry00348, Geometry.check_of_directTraceCheck geometry00348
    checkedPatchCache0346 checkedPatchCache0347
    geometryTraceA00348 geometryTraceB00348 (by decide +kernel)⟩

def checkedGeometry00349 : CheckedGeometry :=
  ⟨geometry00349, Geometry.check_of_directTraceCheck geometry00349
    checkedPatchCache0346 checkedPatchCache0347
    geometryTraceA00349 geometryTraceB00349 (by decide +kernel)⟩

def checkedGeometry00350 : CheckedGeometry :=
  ⟨geometry00350, Geometry.check_of_directTraceCheck geometry00350
    checkedPatchCache0346 checkedPatchCache0347
    geometryTraceA00350 geometryTraceB00350 (by decide +kernel)⟩

def checkedGeometry00351 : CheckedGeometry :=
  ⟨geometry00351, Geometry.check_of_directTraceCheck geometry00351
    checkedPatchCache0346 checkedPatchCache0347
    geometryTraceA00351 geometryTraceB00351 (by decide +kernel)⟩

def checkedGeometry00352 : CheckedGeometry :=
  ⟨geometry00352, Geometry.check_of_directTraceCheck geometry00352
    checkedPatchCache0346 checkedPatchCache0347
    geometryTraceA00352 geometryTraceB00352 (by decide +kernel)⟩

def checkedGeometry00353 : CheckedGeometry :=
  ⟨geometry00353, Geometry.check_of_directTraceCheck geometry00353
    checkedPatchCache0346 checkedPatchCache0347
    geometryTraceA00353 geometryTraceB00353 (by decide +kernel)⟩

def checkedGeometry00354 : CheckedGeometry :=
  ⟨geometry00354, Geometry.check_of_directTraceCheck geometry00354
    checkedPatchCache0346 checkedPatchCache0347
    geometryTraceA00354 geometryTraceB00354 (by decide +kernel)⟩

def checkedGeometry00355 : CheckedGeometry :=
  ⟨geometry00355, Geometry.check_of_directTraceCheck geometry00355
    checkedPatchCache0346 checkedPatchCache0347
    geometryTraceA00355 geometryTraceB00355 (by decide +kernel)⟩

def checkedGeometry00356 : CheckedGeometry :=
  ⟨geometry00356, Geometry.check_of_directTraceCheck geometry00356
    checkedPatchCache0348 checkedPatchCache0349
    geometryTraceA00356 geometryTraceB00356 (by decide +kernel)⟩

def checkedGeometry00357 : CheckedGeometry :=
  ⟨geometry00357, Geometry.check_of_directTraceCheck geometry00357
    checkedPatchCache0348 checkedPatchCache0349
    geometryTraceA00357 geometryTraceB00357 (by decide +kernel)⟩

def checkedGeometry00358 : CheckedGeometry :=
  ⟨geometry00358, Geometry.check_of_directTraceCheck geometry00358
    checkedPatchCache0348 checkedPatchCache0349
    geometryTraceA00358 geometryTraceB00358 (by decide +kernel)⟩

def checkedGeometry00359 : CheckedGeometry :=
  ⟨geometry00359, Geometry.check_of_directTraceCheck geometry00359
    checkedPatchCache0348 checkedPatchCache0349
    geometryTraceA00359 geometryTraceB00359 (by decide +kernel)⟩

def checkedGeometry00360 : CheckedGeometry :=
  ⟨geometry00360, Geometry.check_of_directTraceCheck geometry00360
    checkedPatchCache0348 checkedPatchCache0349
    geometryTraceA00360 geometryTraceB00360 (by decide +kernel)⟩

def checkedGeometry00361 : CheckedGeometry :=
  ⟨geometry00361, Geometry.check_of_directTraceCheck geometry00361
    checkedPatchCache0348 checkedPatchCache0349
    geometryTraceA00361 geometryTraceB00361 (by decide +kernel)⟩

def checkedGeometry00362 : CheckedGeometry :=
  ⟨geometry00362, Geometry.check_of_directTraceCheck geometry00362
    checkedPatchCache0348 checkedPatchCache0349
    geometryTraceA00362 geometryTraceB00362 (by decide +kernel)⟩

def checkedGeometry00363 : CheckedGeometry :=
  ⟨geometry00363, Geometry.check_of_directTraceCheck geometry00363
    checkedPatchCache0350 checkedPatchCache0351
    geometryTraceA00363 geometryTraceB00363 (by decide +kernel)⟩

def checkedGeometry00364 : CheckedGeometry :=
  ⟨geometry00364, Geometry.check_of_directTraceCheck geometry00364
    checkedPatchCache0350 checkedPatchCache0351
    geometryTraceA00364 geometryTraceB00364 (by decide +kernel)⟩

def checkedGeometry00365 : CheckedGeometry :=
  ⟨geometry00365, Geometry.check_of_directTraceCheck geometry00365
    checkedPatchCache0350 checkedPatchCache0351
    geometryTraceA00365 geometryTraceB00365 (by decide +kernel)⟩

def checkedGeometry00366 : CheckedGeometry :=
  ⟨geometry00366, Geometry.check_of_directTraceCheck geometry00366
    checkedPatchCache0350 checkedPatchCache0351
    geometryTraceA00366 geometryTraceB00366 (by decide +kernel)⟩

def checkedGeometry00367 : CheckedGeometry :=
  ⟨geometry00367, Geometry.check_of_directTraceCheck geometry00367
    checkedPatchCache0350 checkedPatchCache0351
    geometryTraceA00367 geometryTraceB00367 (by decide +kernel)⟩

def checkedGeometry00368 : CheckedGeometry :=
  ⟨geometry00368, Geometry.check_of_directTraceCheck geometry00368
    checkedPatchCache0350 checkedPatchCache0351
    geometryTraceA00368 geometryTraceB00368 (by decide +kernel)⟩

def checkedGeometry00369 : CheckedGeometry :=
  ⟨geometry00369, Geometry.check_of_directTraceCheck geometry00369
    checkedPatchCache0350 checkedPatchCache0351
    geometryTraceA00369 geometryTraceB00369 (by decide +kernel)⟩

def checkedGeometry00370 : CheckedGeometry :=
  ⟨geometry00370, Geometry.check_of_directTraceCheck geometry00370
    checkedPatchCache0352 checkedPatchCache0353
    geometryTraceA00370 geometryTraceB00370 (by decide +kernel)⟩

def checkedGeometry00371 : CheckedGeometry :=
  ⟨geometry00371, Geometry.check_of_directTraceCheck geometry00371
    checkedPatchCache0352 checkedPatchCache0353
    geometryTraceA00371 geometryTraceB00371 (by decide +kernel)⟩

def checkedGeometry00372 : CheckedGeometry :=
  ⟨geometry00372, Geometry.check_of_directTraceCheck geometry00372
    checkedPatchCache0352 checkedPatchCache0353
    geometryTraceA00372 geometryTraceB00372 (by decide +kernel)⟩

def checkedGeometry00373 : CheckedGeometry :=
  ⟨geometry00373, Geometry.check_of_directTraceCheck geometry00373
    checkedPatchCache0352 checkedPatchCache0353
    geometryTraceA00373 geometryTraceB00373 (by decide +kernel)⟩

def checkedGeometry00374 : CheckedGeometry :=
  ⟨geometry00374, Geometry.check_of_directTraceCheck geometry00374
    checkedPatchCache0352 checkedPatchCache0353
    geometryTraceA00374 geometryTraceB00374 (by decide +kernel)⟩

def checkedGeometry00375 : CheckedGeometry :=
  ⟨geometry00375, Geometry.check_of_directTraceCheck geometry00375
    checkedPatchCache0352 checkedPatchCache0353
    geometryTraceA00375 geometryTraceB00375 (by decide +kernel)⟩

def checkedGeometry00376 : CheckedGeometry :=
  ⟨geometry00376, Geometry.check_of_directTraceCheck geometry00376
    checkedPatchCache0352 checkedPatchCache0353
    geometryTraceA00376 geometryTraceB00376 (by decide +kernel)⟩

def checkedGeometry00377 : CheckedGeometry :=
  ⟨geometry00377, Geometry.check_of_directTraceCheck geometry00377
    checkedPatchCache0352 checkedPatchCache0353
    geometryTraceA00377 geometryTraceB00377 (by decide +kernel)⟩

def checkedGeometry00378 : CheckedGeometry :=
  ⟨geometry00378, Geometry.check_of_directTraceCheck geometry00378
    checkedPatchCache0354 checkedPatchCache0355
    geometryTraceA00378 geometryTraceB00378 (by decide +kernel)⟩

def checkedGeometry00379 : CheckedGeometry :=
  ⟨geometry00379, Geometry.check_of_directTraceCheck geometry00379
    checkedPatchCache0354 checkedPatchCache0355
    geometryTraceA00379 geometryTraceB00379 (by decide +kernel)⟩

def checkedGeometry00380 : CheckedGeometry :=
  ⟨geometry00380, Geometry.check_of_directTraceCheck geometry00380
    checkedPatchCache0354 checkedPatchCache0355
    geometryTraceA00380 geometryTraceB00380 (by decide +kernel)⟩

def checkedGeometry00381 : CheckedGeometry :=
  ⟨geometry00381, Geometry.check_of_directTraceCheck geometry00381
    checkedPatchCache0354 checkedPatchCache0355
    geometryTraceA00381 geometryTraceB00381 (by decide +kernel)⟩

def checkedGeometry00382 : CheckedGeometry :=
  ⟨geometry00382, Geometry.check_of_directTraceCheck geometry00382
    checkedPatchCache0354 checkedPatchCache0355
    geometryTraceA00382 geometryTraceB00382 (by decide +kernel)⟩

def checkedGeometry00383 : CheckedGeometry :=
  ⟨geometry00383, Geometry.check_of_directTraceCheck geometry00383
    checkedPatchCache0354 checkedPatchCache0355
    geometryTraceA00383 geometryTraceB00383 (by decide +kernel)⟩

def checkedGeometry00384 : CheckedGeometry :=
  ⟨geometry00384, Geometry.check_of_directTraceCheck geometry00384
    checkedPatchCache0354 checkedPatchCache0355
    geometryTraceA00384 geometryTraceB00384 (by decide +kernel)⟩

def checkedGeometry00385 : CheckedGeometry :=
  ⟨geometry00385, Geometry.check_of_directTraceCheck geometry00385
    checkedPatchCache0354 checkedPatchCache0355
    geometryTraceA00385 geometryTraceB00385 (by decide +kernel)⟩

def checkedGeometry00386 : CheckedGeometry :=
  ⟨geometry00386, Geometry.check_of_directTraceCheck geometry00386
    checkedPatchCache0356 checkedPatchCache0357
    geometryTraceA00386 geometryTraceB00386 (by decide +kernel)⟩

def checkedGeometry00387 : CheckedGeometry :=
  ⟨geometry00387, Geometry.check_of_directTraceCheck geometry00387
    checkedPatchCache0356 checkedPatchCache0357
    geometryTraceA00387 geometryTraceB00387 (by decide +kernel)⟩

def checkedGeometry00388 : CheckedGeometry :=
  ⟨geometry00388, Geometry.check_of_directTraceCheck geometry00388
    checkedPatchCache0356 checkedPatchCache0357
    geometryTraceA00388 geometryTraceB00388 (by decide +kernel)⟩

def checkedGeometry00389 : CheckedGeometry :=
  ⟨geometry00389, Geometry.check_of_directTraceCheck geometry00389
    checkedPatchCache0356 checkedPatchCache0357
    geometryTraceA00389 geometryTraceB00389 (by decide +kernel)⟩

def checkedGeometry00390 : CheckedGeometry :=
  ⟨geometry00390, Geometry.check_of_directTraceCheck geometry00390
    checkedPatchCache0356 checkedPatchCache0357
    geometryTraceA00390 geometryTraceB00390 (by decide +kernel)⟩

def checkedGeometry00391 : CheckedGeometry :=
  ⟨geometry00391, Geometry.check_of_directTraceCheck geometry00391
    checkedPatchCache0356 checkedPatchCache0357
    geometryTraceA00391 geometryTraceB00391 (by decide +kernel)⟩

def checkedGeometry00392 : CheckedGeometry :=
  ⟨geometry00392, Geometry.check_of_directTraceCheck geometry00392
    checkedPatchCache0356 checkedPatchCache0357
    geometryTraceA00392 geometryTraceB00392 (by decide +kernel)⟩

def checkedGeometry00393 : CheckedGeometry :=
  ⟨geometry00393, Geometry.check_of_directTraceCheck geometry00393
    checkedPatchCache0356 checkedPatchCache0357
    geometryTraceA00393 geometryTraceB00393 (by decide +kernel)⟩

def checkedGeometry00394 : CheckedGeometry :=
  ⟨geometry00394, Geometry.check_of_directTraceCheck geometry00394
    checkedPatchCache0358 checkedPatchCache0359
    geometryTraceA00394 geometryTraceB00394 (by decide +kernel)⟩

def checkedGeometry00395 : CheckedGeometry :=
  ⟨geometry00395, Geometry.check_of_directTraceCheck geometry00395
    checkedPatchCache0358 checkedPatchCache0359
    geometryTraceA00395 geometryTraceB00395 (by decide +kernel)⟩

def checkedGeometry00396 : CheckedGeometry :=
  ⟨geometry00396, Geometry.check_of_directTraceCheck geometry00396
    checkedPatchCache0358 checkedPatchCache0359
    geometryTraceA00396 geometryTraceB00396 (by decide +kernel)⟩

def checkedGeometry00397 : CheckedGeometry :=
  ⟨geometry00397, Geometry.check_of_directTraceCheck geometry00397
    checkedPatchCache0358 checkedPatchCache0359
    geometryTraceA00397 geometryTraceB00397 (by decide +kernel)⟩

def checkedGeometry00398 : CheckedGeometry :=
  ⟨geometry00398, Geometry.check_of_directTraceCheck geometry00398
    checkedPatchCache0358 checkedPatchCache0359
    geometryTraceA00398 geometryTraceB00398 (by decide +kernel)⟩

def checkedGeometry00399 : CheckedGeometry :=
  ⟨geometry00399, Geometry.check_of_directTraceCheck geometry00399
    checkedPatchCache0358 checkedPatchCache0359
    geometryTraceA00399 geometryTraceB00399 (by decide +kernel)⟩

def checkedGeometry00400 : CheckedGeometry :=
  ⟨geometry00400, Geometry.check_of_directTraceCheck geometry00400
    checkedPatchCache0360 checkedPatchCache0361
    geometryTraceA00400 geometryTraceB00400 (by decide +kernel)⟩

def checkedGeometry00401 : CheckedGeometry :=
  ⟨geometry00401, Geometry.check_of_directTraceCheck geometry00401
    checkedPatchCache0360 checkedPatchCache0361
    geometryTraceA00401 geometryTraceB00401 (by decide +kernel)⟩

def checkedGeometry00402 : CheckedGeometry :=
  ⟨geometry00402, Geometry.check_of_directTraceCheck geometry00402
    checkedPatchCache0360 checkedPatchCache0361
    geometryTraceA00402 geometryTraceB00402 (by decide +kernel)⟩

def checkedGeometry00403 : CheckedGeometry :=
  ⟨geometry00403, Geometry.check_of_directTraceCheck geometry00403
    checkedPatchCache0360 checkedPatchCache0361
    geometryTraceA00403 geometryTraceB00403 (by decide +kernel)⟩

def checkedGeometry00404 : CheckedGeometry :=
  ⟨geometry00404, Geometry.check_of_directTraceCheck geometry00404
    checkedPatchCache0360 checkedPatchCache0361
    geometryTraceA00404 geometryTraceB00404 (by decide +kernel)⟩

def checkedGeometry00405 : CheckedGeometry :=
  ⟨geometry00405, Geometry.check_of_directTraceCheck geometry00405
    checkedPatchCache0360 checkedPatchCache0361
    geometryTraceA00405 geometryTraceB00405 (by decide +kernel)⟩

def checkedGeometry00406 : CheckedGeometry :=
  ⟨geometry00406, Geometry.check_of_directTraceCheck geometry00406
    checkedPatchCache0360 checkedPatchCache0361
    geometryTraceA00406 geometryTraceB00406 (by decide +kernel)⟩

def checkedGeometry00407 : CheckedGeometry :=
  ⟨geometry00407, Geometry.check_of_directTraceCheck geometry00407
    checkedPatchCache0362 checkedPatchCache0363
    geometryTraceA00407 geometryTraceB00407 (by decide +kernel)⟩

def checkedGeometry00408 : CheckedGeometry :=
  ⟨geometry00408, Geometry.check_of_directTraceCheck geometry00408
    checkedPatchCache0362 checkedPatchCache0363
    geometryTraceA00408 geometryTraceB00408 (by decide +kernel)⟩

def checkedGeometry00409 : CheckedGeometry :=
  ⟨geometry00409, Geometry.check_of_directTraceCheck geometry00409
    checkedPatchCache0362 checkedPatchCache0363
    geometryTraceA00409 geometryTraceB00409 (by decide +kernel)⟩

def checkedGeometry00410 : CheckedGeometry :=
  ⟨geometry00410, Geometry.check_of_directTraceCheck geometry00410
    checkedPatchCache0362 checkedPatchCache0363
    geometryTraceA00410 geometryTraceB00410 (by decide +kernel)⟩

def checkedGeometry00411 : CheckedGeometry :=
  ⟨geometry00411, Geometry.check_of_directTraceCheck geometry00411
    checkedPatchCache0362 checkedPatchCache0363
    geometryTraceA00411 geometryTraceB00411 (by decide +kernel)⟩

def checkedGeometry00412 : CheckedGeometry :=
  ⟨geometry00412, Geometry.check_of_directTraceCheck geometry00412
    checkedPatchCache0362 checkedPatchCache0363
    geometryTraceA00412 geometryTraceB00412 (by decide +kernel)⟩

def checkedGeometry00413 : CheckedGeometry :=
  ⟨geometry00413, Geometry.check_of_directTraceCheck geometry00413
    checkedPatchCache0362 checkedPatchCache0363
    geometryTraceA00413 geometryTraceB00413 (by decide +kernel)⟩

def checkedGeometry00414 : CheckedGeometry :=
  ⟨geometry00414, Geometry.check_of_directTraceCheck geometry00414
    checkedPatchCache0362 checkedPatchCache0363
    geometryTraceA00414 geometryTraceB00414 (by decide +kernel)⟩

def checkedGeometry00415 : CheckedGeometry :=
  ⟨geometry00415, Geometry.check_of_directTraceCheck geometry00415
    checkedPatchCache0364 checkedPatchCache0365
    geometryTraceA00415 geometryTraceB00415 (by decide +kernel)⟩

def checkedGeometry00416 : CheckedGeometry :=
  ⟨geometry00416, Geometry.check_of_directTraceCheck geometry00416
    checkedPatchCache0364 checkedPatchCache0365
    geometryTraceA00416 geometryTraceB00416 (by decide +kernel)⟩

def checkedGeometry00417 : CheckedGeometry :=
  ⟨geometry00417, Geometry.check_of_directTraceCheck geometry00417
    checkedPatchCache0364 checkedPatchCache0365
    geometryTraceA00417 geometryTraceB00417 (by decide +kernel)⟩

def checkedGeometry00418 : CheckedGeometry :=
  ⟨geometry00418, Geometry.check_of_directTraceCheck geometry00418
    checkedPatchCache0364 checkedPatchCache0365
    geometryTraceA00418 geometryTraceB00418 (by decide +kernel)⟩

def checkedGeometry00419 : CheckedGeometry :=
  ⟨geometry00419, Geometry.check_of_directTraceCheck geometry00419
    checkedPatchCache0364 checkedPatchCache0365
    geometryTraceA00419 geometryTraceB00419 (by decide +kernel)⟩

def checkedGeometry00420 : CheckedGeometry :=
  ⟨geometry00420, Geometry.check_of_directTraceCheck geometry00420
    checkedPatchCache0364 checkedPatchCache0365
    geometryTraceA00420 geometryTraceB00420 (by decide +kernel)⟩

def checkedGeometry00421 : CheckedGeometry :=
  ⟨geometry00421, Geometry.check_of_directTraceCheck geometry00421
    checkedPatchCache0364 checkedPatchCache0365
    geometryTraceA00421 geometryTraceB00421 (by decide +kernel)⟩

def checkedGeometry00422 : CheckedGeometry :=
  ⟨geometry00422, Geometry.check_of_directTraceCheck geometry00422
    checkedPatchCache0364 checkedPatchCache0365
    geometryTraceA00422 geometryTraceB00422 (by decide +kernel)⟩

def checkedGeometry00423 : CheckedGeometry :=
  ⟨geometry00423, Geometry.check_of_directTraceCheck geometry00423
    checkedPatchCache0364 checkedPatchCache0365
    geometryTraceA00423 geometryTraceB00423 (by decide +kernel)⟩

def checkedGeometry00424 : CheckedGeometry :=
  ⟨geometry00424, Geometry.check_of_directTraceCheck geometry00424
    checkedPatchCache0366 checkedPatchCache0367
    geometryTraceA00424 geometryTraceB00424 (by decide +kernel)⟩

def checkedGeometry00425 : CheckedGeometry :=
  ⟨geometry00425, Geometry.check_of_directTraceCheck geometry00425
    checkedPatchCache0366 checkedPatchCache0367
    geometryTraceA00425 geometryTraceB00425 (by decide +kernel)⟩

def checkedGeometry00426 : CheckedGeometry :=
  ⟨geometry00426, Geometry.check_of_directTraceCheck geometry00426
    checkedPatchCache0366 checkedPatchCache0367
    geometryTraceA00426 geometryTraceB00426 (by decide +kernel)⟩

def checkedGeometry00427 : CheckedGeometry :=
  ⟨geometry00427, Geometry.check_of_directTraceCheck geometry00427
    checkedPatchCache0366 checkedPatchCache0367
    geometryTraceA00427 geometryTraceB00427 (by decide +kernel)⟩

def checkedGeometry00428 : CheckedGeometry :=
  ⟨geometry00428, Geometry.check_of_directTraceCheck geometry00428
    checkedPatchCache0366 checkedPatchCache0367
    geometryTraceA00428 geometryTraceB00428 (by decide +kernel)⟩

def checkedGeometry00429 : CheckedGeometry :=
  ⟨geometry00429, Geometry.check_of_directTraceCheck geometry00429
    checkedPatchCache0366 checkedPatchCache0367
    geometryTraceA00429 geometryTraceB00429 (by decide +kernel)⟩

def checkedGeometry00430 : CheckedGeometry :=
  ⟨geometry00430, Geometry.check_of_directTraceCheck geometry00430
    checkedPatchCache0366 checkedPatchCache0367
    geometryTraceA00430 geometryTraceB00430 (by decide +kernel)⟩

def checkedGeometry00431 : CheckedGeometry :=
  ⟨geometry00431, Geometry.check_of_directTraceCheck geometry00431
    checkedPatchCache0368 checkedPatchCache0369
    geometryTraceA00431 geometryTraceB00431 (by decide +kernel)⟩

def checkedGeometry00432 : CheckedGeometry :=
  ⟨geometry00432, Geometry.check_of_directTraceCheck geometry00432
    checkedPatchCache0368 checkedPatchCache0369
    geometryTraceA00432 geometryTraceB00432 (by decide +kernel)⟩

def checkedGeometry00433 : CheckedGeometry :=
  ⟨geometry00433, Geometry.check_of_directTraceCheck geometry00433
    checkedPatchCache0368 checkedPatchCache0369
    geometryTraceA00433 geometryTraceB00433 (by decide +kernel)⟩

def checkedGeometry00434 : CheckedGeometry :=
  ⟨geometry00434, Geometry.check_of_directTraceCheck geometry00434
    checkedPatchCache0368 checkedPatchCache0369
    geometryTraceA00434 geometryTraceB00434 (by decide +kernel)⟩

def checkedGeometry00435 : CheckedGeometry :=
  ⟨geometry00435, Geometry.check_of_directTraceCheck geometry00435
    checkedPatchCache0368 checkedPatchCache0369
    geometryTraceA00435 geometryTraceB00435 (by decide +kernel)⟩

def checkedGeometry00436 : CheckedGeometry :=
  ⟨geometry00436, Geometry.check_of_directTraceCheck geometry00436
    checkedPatchCache0368 checkedPatchCache0369
    geometryTraceA00436 geometryTraceB00436 (by decide +kernel)⟩

def checkedGeometry00437 : CheckedGeometry :=
  ⟨geometry00437, Geometry.check_of_directTraceCheck geometry00437
    checkedPatchCache0368 checkedPatchCache0369
    geometryTraceA00437 geometryTraceB00437 (by decide +kernel)⟩

def checkedGeometry00438 : CheckedGeometry :=
  ⟨geometry00438, Geometry.check_of_directTraceCheck geometry00438
    checkedPatchCache0370 checkedPatchCache0371
    geometryTraceA00438 geometryTraceB00438 (by decide +kernel)⟩

def checkedGeometry00439 : CheckedGeometry :=
  ⟨geometry00439, Geometry.check_of_directTraceCheck geometry00439
    checkedPatchCache0370 checkedPatchCache0371
    geometryTraceA00439 geometryTraceB00439 (by decide +kernel)⟩

def checkedGeometry00440 : CheckedGeometry :=
  ⟨geometry00440, Geometry.check_of_directTraceCheck geometry00440
    checkedPatchCache0370 checkedPatchCache0371
    geometryTraceA00440 geometryTraceB00440 (by decide +kernel)⟩

def checkedGeometry00441 : CheckedGeometry :=
  ⟨geometry00441, Geometry.check_of_directTraceCheck geometry00441
    checkedPatchCache0370 checkedPatchCache0371
    geometryTraceA00441 geometryTraceB00441 (by decide +kernel)⟩

def checkedGeometry00442 : CheckedGeometry :=
  ⟨geometry00442, Geometry.check_of_directTraceCheck geometry00442
    checkedPatchCache0370 checkedPatchCache0371
    geometryTraceA00442 geometryTraceB00442 (by decide +kernel)⟩

def checkedGeometry00443 : CheckedGeometry :=
  ⟨geometry00443, Geometry.check_of_directTraceCheck geometry00443
    checkedPatchCache0370 checkedPatchCache0371
    geometryTraceA00443 geometryTraceB00443 (by decide +kernel)⟩

def checkedGeometry00444 : CheckedGeometry :=
  ⟨geometry00444, Geometry.check_of_directTraceCheck geometry00444
    checkedPatchCache0370 checkedPatchCache0371
    geometryTraceA00444 geometryTraceB00444 (by decide +kernel)⟩

def checkedGeometry00445 : CheckedGeometry :=
  ⟨geometry00445, Geometry.check_of_directTraceCheck geometry00445
    checkedPatchCache0370 checkedPatchCache0371
    geometryTraceA00445 geometryTraceB00445 (by decide +kernel)⟩

def checkedGeometry00446 : CheckedGeometry :=
  ⟨geometry00446, Geometry.check_of_directTraceCheck geometry00446
    checkedPatchCache0372 checkedPatchCache0373
    geometryTraceA00446 geometryTraceB00446 (by decide +kernel)⟩

def checkedGeometry00447 : CheckedGeometry :=
  ⟨geometry00447, Geometry.check_of_directTraceCheck geometry00447
    checkedPatchCache0372 checkedPatchCache0373
    geometryTraceA00447 geometryTraceB00447 (by decide +kernel)⟩

def checkedGeometry00448 : CheckedGeometry :=
  ⟨geometry00448, Geometry.check_of_directTraceCheck geometry00448
    checkedPatchCache0372 checkedPatchCache0373
    geometryTraceA00448 geometryTraceB00448 (by decide +kernel)⟩

def checkedGeometry00449 : CheckedGeometry :=
  ⟨geometry00449, Geometry.check_of_directTraceCheck geometry00449
    checkedPatchCache0372 checkedPatchCache0373
    geometryTraceA00449 geometryTraceB00449 (by decide +kernel)⟩

def checkedGeometry00450 : CheckedGeometry :=
  ⟨geometry00450, Geometry.check_of_directTraceCheck geometry00450
    checkedPatchCache0372 checkedPatchCache0373
    geometryTraceA00450 geometryTraceB00450 (by decide +kernel)⟩

def checkedGeometry00451 : CheckedGeometry :=
  ⟨geometry00451, Geometry.check_of_directTraceCheck geometry00451
    checkedPatchCache0372 checkedPatchCache0373
    geometryTraceA00451 geometryTraceB00451 (by decide +kernel)⟩

def checkedGeometry00452 : CheckedGeometry :=
  ⟨geometry00452, Geometry.check_of_directTraceCheck geometry00452
    checkedPatchCache0372 checkedPatchCache0373
    geometryTraceA00452 geometryTraceB00452 (by decide +kernel)⟩

def checkedGeometry00453 : CheckedGeometry :=
  ⟨geometry00453, Geometry.check_of_directTraceCheck geometry00453
    checkedPatchCache0372 checkedPatchCache0373
    geometryTraceA00453 geometryTraceB00453 (by decide +kernel)⟩

def checkedGeometry00454 : CheckedGeometry :=
  ⟨geometry00454, Geometry.check_of_directTraceCheck geometry00454
    checkedPatchCache0372 checkedPatchCache0373
    geometryTraceA00454 geometryTraceB00454 (by decide +kernel)⟩

def checkedGeometry00455 : CheckedGeometry :=
  ⟨geometry00455, Geometry.check_of_directTraceCheck geometry00455
    checkedPatchCache0374 checkedPatchCache0375
    geometryTraceA00455 geometryTraceB00455 (by decide +kernel)⟩

def checkedGeometry00456 : CheckedGeometry :=
  ⟨geometry00456, Geometry.check_of_directTraceCheck geometry00456
    checkedPatchCache0374 checkedPatchCache0375
    geometryTraceA00456 geometryTraceB00456 (by decide +kernel)⟩

def checkedGeometry00457 : CheckedGeometry :=
  ⟨geometry00457, Geometry.check_of_directTraceCheck geometry00457
    checkedPatchCache0374 checkedPatchCache0375
    geometryTraceA00457 geometryTraceB00457 (by decide +kernel)⟩

def checkedGeometry00458 : CheckedGeometry :=
  ⟨geometry00458, Geometry.check_of_directTraceCheck geometry00458
    checkedPatchCache0374 checkedPatchCache0375
    geometryTraceA00458 geometryTraceB00458 (by decide +kernel)⟩

def checkedGeometry00459 : CheckedGeometry :=
  ⟨geometry00459, Geometry.check_of_directTraceCheck geometry00459
    checkedPatchCache0374 checkedPatchCache0375
    geometryTraceA00459 geometryTraceB00459 (by decide +kernel)⟩

def checkedGeometry00460 : CheckedGeometry :=
  ⟨geometry00460, Geometry.check_of_directTraceCheck geometry00460
    checkedPatchCache0374 checkedPatchCache0375
    geometryTraceA00460 geometryTraceB00460 (by decide +kernel)⟩

def checkedGeometry00461 : CheckedGeometry :=
  ⟨geometry00461, Geometry.check_of_directTraceCheck geometry00461
    checkedPatchCache0376 checkedPatchCache0377
    geometryTraceA00461 geometryTraceB00461 (by decide +kernel)⟩

def checkedGeometry00462 : CheckedGeometry :=
  ⟨geometry00462, Geometry.check_of_directTraceCheck geometry00462
    checkedPatchCache0376 checkedPatchCache0377
    geometryTraceA00462 geometryTraceB00462 (by decide +kernel)⟩

def checkedGeometry00463 : CheckedGeometry :=
  ⟨geometry00463, Geometry.check_of_directTraceCheck geometry00463
    checkedPatchCache0376 checkedPatchCache0377
    geometryTraceA00463 geometryTraceB00463 (by decide +kernel)⟩

def checkedGeometry00464 : CheckedGeometry :=
  ⟨geometry00464, Geometry.check_of_directTraceCheck geometry00464
    checkedPatchCache0376 checkedPatchCache0377
    geometryTraceA00464 geometryTraceB00464 (by decide +kernel)⟩

def checkedGeometry00465 : CheckedGeometry :=
  ⟨geometry00465, Geometry.check_of_directTraceCheck geometry00465
    checkedPatchCache0376 checkedPatchCache0377
    geometryTraceA00465 geometryTraceB00465 (by decide +kernel)⟩

def checkedGeometry00466 : CheckedGeometry :=
  ⟨geometry00466, Geometry.check_of_directTraceCheck geometry00466
    checkedPatchCache0376 checkedPatchCache0377
    geometryTraceA00466 geometryTraceB00466 (by decide +kernel)⟩

def checkedGeometry00467 : CheckedGeometry :=
  ⟨geometry00467, Geometry.check_of_directTraceCheck geometry00467
    checkedPatchCache0376 checkedPatchCache0377
    geometryTraceA00467 geometryTraceB00467 (by decide +kernel)⟩

def checkedGeometry00468 : CheckedGeometry :=
  ⟨geometry00468, Geometry.check_of_directTraceCheck geometry00468
    checkedPatchCache0376 checkedPatchCache0377
    geometryTraceA00468 geometryTraceB00468 (by decide +kernel)⟩

def checkedGeometry00469 : CheckedGeometry :=
  ⟨geometry00469, Geometry.check_of_directTraceCheck geometry00469
    checkedPatchCache0376 checkedPatchCache0377
    geometryTraceA00469 geometryTraceB00469 (by decide +kernel)⟩

def checkedGeometry00470 : CheckedGeometry :=
  ⟨geometry00470, Geometry.check_of_directTraceCheck geometry00470
    checkedPatchCache0378 checkedPatchCache0379
    geometryTraceA00470 geometryTraceB00470 (by decide +kernel)⟩

def checkedGeometry00471 : CheckedGeometry :=
  ⟨geometry00471, Geometry.check_of_directTraceCheck geometry00471
    checkedPatchCache0378 checkedPatchCache0379
    geometryTraceA00471 geometryTraceB00471 (by decide +kernel)⟩

def checkedGeometry00472 : CheckedGeometry :=
  ⟨geometry00472, Geometry.check_of_directTraceCheck geometry00472
    checkedPatchCache0378 checkedPatchCache0379
    geometryTraceA00472 geometryTraceB00472 (by decide +kernel)⟩

def checkedGeometry00473 : CheckedGeometry :=
  ⟨geometry00473, Geometry.check_of_directTraceCheck geometry00473
    checkedPatchCache0378 checkedPatchCache0379
    geometryTraceA00473 geometryTraceB00473 (by decide +kernel)⟩

def checkedGeometry00474 : CheckedGeometry :=
  ⟨geometry00474, Geometry.check_of_directTraceCheck geometry00474
    checkedPatchCache0378 checkedPatchCache0379
    geometryTraceA00474 geometryTraceB00474 (by decide +kernel)⟩

def checkedGeometry00475 : CheckedGeometry :=
  ⟨geometry00475, Geometry.check_of_directTraceCheck geometry00475
    checkedPatchCache0378 checkedPatchCache0379
    geometryTraceA00475 geometryTraceB00475 (by decide +kernel)⟩

def checkedGeometry00476 : CheckedGeometry :=
  ⟨geometry00476, Geometry.check_of_directTraceCheck geometry00476
    checkedPatchCache0378 checkedPatchCache0379
    geometryTraceA00476 geometryTraceB00476 (by decide +kernel)⟩

def checkedGeometry00477 : CheckedGeometry :=
  ⟨geometry00477, Geometry.check_of_directTraceCheck geometry00477
    checkedPatchCache0378 checkedPatchCache0379
    geometryTraceA00477 geometryTraceB00477 (by decide +kernel)⟩

def checkedGeometry00478 : CheckedGeometry :=
  ⟨geometry00478, Geometry.check_of_directTraceCheck geometry00478
    checkedPatchCache0380 checkedPatchCache0381
    geometryTraceA00478 geometryTraceB00478 (by decide +kernel)⟩

def checkedGeometry00479 : CheckedGeometry :=
  ⟨geometry00479, Geometry.check_of_directTraceCheck geometry00479
    checkedPatchCache0380 checkedPatchCache0381
    geometryTraceA00479 geometryTraceB00479 (by decide +kernel)⟩

def checkedGeometry00480 : CheckedGeometry :=
  ⟨geometry00480, Geometry.check_of_directTraceCheck geometry00480
    checkedPatchCache0380 checkedPatchCache0381
    geometryTraceA00480 geometryTraceB00480 (by decide +kernel)⟩

def checkedGeometry00481 : CheckedGeometry :=
  ⟨geometry00481, Geometry.check_of_directTraceCheck geometry00481
    checkedPatchCache0380 checkedPatchCache0381
    geometryTraceA00481 geometryTraceB00481 (by decide +kernel)⟩

def checkedGeometry00482 : CheckedGeometry :=
  ⟨geometry00482, Geometry.check_of_directTraceCheck geometry00482
    checkedPatchCache0380 checkedPatchCache0381
    geometryTraceA00482 geometryTraceB00482 (by decide +kernel)⟩

def checkedGeometry00483 : CheckedGeometry :=
  ⟨geometry00483, Geometry.check_of_directTraceCheck geometry00483
    checkedPatchCache0380 checkedPatchCache0381
    geometryTraceA00483 geometryTraceB00483 (by decide +kernel)⟩

def checkedGeometry00484 : CheckedGeometry :=
  ⟨geometry00484, Geometry.check_of_directTraceCheck geometry00484
    checkedPatchCache0380 checkedPatchCache0381
    geometryTraceA00484 geometryTraceB00484 (by decide +kernel)⟩

def checkedGeometry00485 : CheckedGeometry :=
  ⟨geometry00485, Geometry.check_of_directTraceCheck geometry00485
    checkedPatchCache0382 checkedPatchCache0383
    geometryTraceA00485 geometryTraceB00485 (by decide +kernel)⟩

def checkedGeometry00486 : CheckedGeometry :=
  ⟨geometry00486, Geometry.check_of_directTraceCheck geometry00486
    checkedPatchCache0382 checkedPatchCache0383
    geometryTraceA00486 geometryTraceB00486 (by decide +kernel)⟩

def checkedGeometry00487 : CheckedGeometry :=
  ⟨geometry00487, Geometry.check_of_directTraceCheck geometry00487
    checkedPatchCache0382 checkedPatchCache0383
    geometryTraceA00487 geometryTraceB00487 (by decide +kernel)⟩

def checkedGeometry00488 : CheckedGeometry :=
  ⟨geometry00488, Geometry.check_of_directTraceCheck geometry00488
    checkedPatchCache0382 checkedPatchCache0383
    geometryTraceA00488 geometryTraceB00488 (by decide +kernel)⟩

def checkedGeometry00489 : CheckedGeometry :=
  ⟨geometry00489, Geometry.check_of_directTraceCheck geometry00489
    checkedPatchCache0382 checkedPatchCache0383
    geometryTraceA00489 geometryTraceB00489 (by decide +kernel)⟩

def checkedGeometry00490 : CheckedGeometry :=
  ⟨geometry00490, Geometry.check_of_directTraceCheck geometry00490
    checkedPatchCache0382 checkedPatchCache0383
    geometryTraceA00490 geometryTraceB00490 (by decide +kernel)⟩

def checkedGeometry00491 : CheckedGeometry :=
  ⟨geometry00491, Geometry.check_of_directTraceCheck geometry00491
    checkedPatchCache0382 checkedPatchCache0383
    geometryTraceA00491 geometryTraceB00491 (by decide +kernel)⟩

def checkedGeometry00492 : CheckedGeometry :=
  ⟨geometry00492, Geometry.check_of_directTraceCheck geometry00492
    checkedPatchCache0382 checkedPatchCache0383
    geometryTraceA00492 geometryTraceB00492 (by decide +kernel)⟩

def checkedGeometry00493 : CheckedGeometry :=
  ⟨geometry00493, Geometry.check_of_directTraceCheck geometry00493
    checkedPatchCache0382 checkedPatchCache0383
    geometryTraceA00493 geometryTraceB00493 (by decide +kernel)⟩

def checkedGeometry00494 : CheckedGeometry :=
  ⟨geometry00494, Geometry.check_of_directTraceCheck geometry00494
    checkedPatchCache0384 checkedPatchCache0385
    geometryTraceA00494 geometryTraceB00494 (by decide +kernel)⟩

def checkedGeometry00495 : CheckedGeometry :=
  ⟨geometry00495, Geometry.check_of_directTraceCheck geometry00495
    checkedPatchCache0386 checkedPatchCache0387
    geometryTraceA00495 geometryTraceB00495 (by decide +kernel)⟩

def checkedGeometry00496 : CheckedGeometry :=
  ⟨geometry00496, Geometry.check_of_directTraceCheck geometry00496
    checkedPatchCache0388 checkedPatchCache0389
    geometryTraceA00496 geometryTraceB00496 (by decide +kernel)⟩

def checkedGeometry00497 : CheckedGeometry :=
  ⟨geometry00497, Geometry.check_of_directTraceCheck geometry00497
    checkedPatchCache0390 checkedPatchCache0391
    geometryTraceA00497 geometryTraceB00497 (by decide +kernel)⟩

def checkedGeometry00498 : CheckedGeometry :=
  ⟨geometry00498, Geometry.check_of_directTraceCheck geometry00498
    checkedPatchCache0392 checkedPatchCache0393
    geometryTraceA00498 geometryTraceB00498 (by decide +kernel)⟩

def checkedGeometry00499 : CheckedGeometry :=
  ⟨geometry00499, Geometry.check_of_directTraceCheck geometry00499
    checkedPatchCache0394 checkedPatchCache0395
    geometryTraceA00499 geometryTraceB00499 (by decide +kernel)⟩

def checkedGeometry00500 : CheckedGeometry :=
  ⟨geometry00500, Geometry.check_of_directTraceCheck geometry00500
    checkedPatchCache0396 checkedPatchCache0397
    geometryTraceA00500 geometryTraceB00500 (by decide +kernel)⟩

def checkedGeometry00501 : CheckedGeometry :=
  ⟨geometry00501, Geometry.check_of_directTraceCheck geometry00501
    checkedPatchCache0398 checkedPatchCache0399
    geometryTraceA00501 geometryTraceB00501 (by decide +kernel)⟩

def checkedGeometry00502 : CheckedGeometry :=
  ⟨geometry00502, Geometry.check_of_directTraceCheck geometry00502
    checkedPatchCache0400 checkedPatchCache0401
    geometryTraceA00502 geometryTraceB00502 (by decide +kernel)⟩

def checkedGeometry00503 : CheckedGeometry :=
  ⟨geometry00503, Geometry.check_of_directTraceCheck geometry00503
    checkedPatchCache0402 checkedPatchCache0403
    geometryTraceA00503 geometryTraceB00503 (by decide +kernel)⟩

def checkedGeometry00504 : CheckedGeometry :=
  ⟨geometry00504, Geometry.check_of_directTraceCheck geometry00504
    checkedPatchCache0404 checkedPatchCache0405
    geometryTraceA00504 geometryTraceB00504 (by decide +kernel)⟩

def checkedGeometry00505 : CheckedGeometry :=
  ⟨geometry00505, Geometry.check_of_directTraceCheck geometry00505
    checkedPatchCache0406 checkedPatchCache0407
    geometryTraceA00505 geometryTraceB00505 (by decide +kernel)⟩

def checkedGeometry00506 : CheckedGeometry :=
  ⟨geometry00506, Geometry.check_of_directTraceCheck geometry00506
    checkedPatchCache0408 checkedPatchCache0409
    geometryTraceA00506 geometryTraceB00506 (by decide +kernel)⟩

def checkedGeometry00507 : CheckedGeometry :=
  ⟨geometry00507, Geometry.check_of_directTraceCheck geometry00507
    checkedPatchCache0410 checkedPatchCache0411
    geometryTraceA00507 geometryTraceB00507 (by decide +kernel)⟩

def checkedGeometry00508 : CheckedGeometry :=
  ⟨geometry00508, Geometry.check_of_directTraceCheck geometry00508
    checkedPatchCache0412 checkedPatchCache0413
    geometryTraceA00508 geometryTraceB00508 (by decide +kernel)⟩

def checkedGeometry00509 : CheckedGeometry :=
  ⟨geometry00509, Geometry.check_of_directTraceCheck geometry00509
    checkedPatchCache0414 checkedPatchCache0415
    geometryTraceA00509 geometryTraceB00509 (by decide +kernel)⟩

def checkedGeometry00510 : CheckedGeometry :=
  ⟨geometry00510, Geometry.check_of_directTraceCheck geometry00510
    checkedPatchCache0416 checkedPatchCache0417
    geometryTraceA00510 geometryTraceB00510 (by decide +kernel)⟩

def checkedGeometry00511 : CheckedGeometry :=
  ⟨geometry00511, Geometry.check_of_directTraceCheck geometry00511
    checkedPatchCache0418 checkedPatchCache0419
    geometryTraceA00511 geometryTraceB00511 (by decide +kernel)⟩


end
end ErdosOverlap.Native6Leaves
