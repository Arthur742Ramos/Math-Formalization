import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Lean.Elab.Tactic.Decide

/-! SOURCE ONLY / UNCOMPILED. Ordinary kernel-reduction `by decide` candidates.
No native_decide, custom axiom, or external checker result is used as a premise.
The actual SSet interpretation is a separate obligation. -/
namespace AutomaticCoherence.RelativeLastVertexLeanCertificate01

abbrev Cell := List Nat
structure Pair where
  sigma : Cell
  missing : Nat
  deriving DecidableEq, Inhabited

def cut (n : Nat) : Nat := 2 ^ (n + 1)
/-- Exactly the codes 1 through 2^(n+1)+n, with no invalid zero code. -/
def vertices (n : Nat) : List Nat := (List.range (cut n + n)).map (· + 1)
abbrev Vertex (n : Nat) := Fin (cut n + n)
def vertexCode {n : Nat} (v : Vertex n) : Nat := v.val + 1
/-- Lower codes are nonempty bit subsets; upper codes are cut+p.
Subset and max comparisons are expressed without an ambient ordering of faces. -/
def strict (n a b : Nat) : Bool :=
  if a < cut n then
    if b < cut n then
      (!(a == b)) && (List.range (n+1)).all (fun j => !a.testBit j || b.testBit j)
    else (List.range (n+1)).all (fun j => !a.testBit j || decide (j ≤ b-cut n))
  else decide (cut n ≤ b ∧ a < b)
def vertexLE {n : Nat} (a b : Vertex n) : Prop :=
  a = b ∨ strict n (vertexCode a) (vertexCode b) = true

/-- All nonempty strict chains, constructed from the finite vertex list.
A strict subset has smaller numeric code, so the listed order is topological. -/
def chains (n : Nat) : List Nat → List Cell
  | [] => []
  | v :: vs =>
    let rest := chains n vs
    [v] :: (rest ++ (rest.filter (fun c => c.all (strict n v))).map (v :: ·))
def «universe» (n : Nat) : List Cell := chains n (vertices n)
def subfaces : Cell → List Cell
  | [] => []
  | v :: vs => let rest := subfaces vs; [v] :: (rest ++ rest.map (v :: ·))
def covers (n v j : Nat) : Bool :=
  if v < cut n then v.testBit j else v-cut n == j
def initialCell (n : Nat) (c : Cell) : Bool :=
  c.all (fun v => decide (v < cut n)) ||
    !((List.range (n+1)).all (fun j => c.any (fun v => covers n v j)))
def initial (n : Nat) : List Cell := («universe» n).filter (initialCell n)
def lower (p : Pair) : Cell := p.sigma.eraseIdx p.missing
def live (n : Nat) (prior : List Pair) : List Cell :=
  initial n ++ prior.flatMap (fun p => [p.sigma, lower p])
def sameSet (s t : List Cell) : Bool := s.all t.contains && t.all s.contains
def horn (p : Pair) : List Cell :=
  ((List.range p.sigma.length).filter (fun j => !(j == p.missing))).flatMap
    (fun j => subfaces (p.sigma.eraseIdx j))
def distinct {α : Type} [BEq α] : List α → Bool
  | [] => true
  | a :: l => !l.contains a && distinct l
def orderCheck (n : Nat) : Bool :=
  let vs := vertices n
  vs.all (fun a => !strict n a a) &&
  vs.all (fun a => vs.all (fun b => !(strict n a b && strict n b a))) &&
  vs.all (fun a => vs.all (fun b => vs.all (fun c =>
    !(strict n a b && strict n b c) || strict n a c)))
def initialCheck (n : Nat) : Bool :=
  distinct («universe» n) && (initial n).all (fun c => (subfaces c).all (initial n).contains)
def stepCheck (n : Nat) (prior : List Pair) (p : Pair) : Bool :=
  let old := live n prior
  («universe» n).contains p.sigma && decide (2 ≤ p.sigma.length) &&
    decide (p.missing < p.sigma.length) &&
    !old.contains p.sigma && !old.contains (lower p) &&
    sameSet ((subfaces p.sigma).filter old.contains) (horn p) &&
    sameSet ((subfaces p.sigma).filter (fun c => !old.contains c)) [p.sigma, lower p] &&
    ((subfaces (lower p)).filter (fun c => !(c == lower p))).all old.contains
def coverageCheck (n : Nat) (ps : List Pair) : Bool := sameSet (live n ps) («universe» n)
def rankCheck (ps : List Pair) : Bool :=
  (List.range ps.length).all (fun y => (List.range ps.length).all (fun x =>
    x == y || !((subfaces (ps.getD y default).sigma).contains (lower (ps.getD x default))) ||
      decide (x < y)))

def pairs0 : List Pair := [
  ⟨[1, 2], 0⟩]

theorem order_check_0 : orderCheck 0 = true := by decide +kernel
theorem initial_check_0 : initialCheck 0 = true := by decide +kernel
theorem cell_count_0 : («universe» 0).length = 3 := by decide +kernel
theorem initial_count_0 : (initial 0).length = 1 := by decide +kernel
theorem step_0_00 : stepCheck 0 (pairs0.take 0) (pairs0.getD 0 default) = true := by decide +kernel
theorem coverage_check_0 : coverageCheck 0 pairs0 = true := by decide +kernel
theorem rank_check_0 : rankCheck pairs0 = true := by decide +kernel

def pairs1 : List Pair := [
  ⟨[2, 3, 5], 0⟩,
  ⟨[1, 3, 5], 1⟩,
  ⟨[1, 4, 5], 0⟩]

theorem order_check_1 : orderCheck 1 = true := by decide +kernel
theorem initial_check_1 : initialCheck 1 = true := by decide +kernel
theorem cell_count_1 : («universe» 1).length = 15 := by decide +kernel
theorem initial_count_1 : (initial 1).length = 9 := by decide +kernel
theorem step_1_00 : stepCheck 1 (pairs1.take 0) (pairs1.getD 0 default) = true := by decide +kernel
theorem step_1_01 : stepCheck 1 (pairs1.take 1) (pairs1.getD 1 default) = true := by decide +kernel
theorem step_1_02 : stepCheck 1 (pairs1.take 2) (pairs1.getD 2 default) = true := by decide +kernel
theorem coverage_check_1 : coverageCheck 1 pairs1 = true := by decide +kernel
theorem rank_check_1 : rankCheck pairs1 = true := by decide +kernel

def pairs2 : List Pair := [
  ⟨[1, 3, 10], 0⟩,
  ⟨[1, 7, 10], 0⟩,
  ⟨[1, 3, 7, 10], 0⟩,
  ⟨[1, 5, 7, 10], 0⟩,
  ⟨[4, 5, 7, 10], 1⟩,
  ⟨[4, 6, 7, 10], 0⟩,
  ⟨[2, 6, 7, 10], 1⟩,
  ⟨[2, 3, 7, 10], 2⟩,
  ⟨[2, 3, 9, 10], 0⟩,
  ⟨[1, 3, 9, 10], 1⟩,
  ⟨[1, 8, 9, 10], 0⟩]

theorem order_check_2 : orderCheck 2 = true := by decide +kernel
theorem initial_check_2 : initialCheck 2 = true := by decide +kernel
theorem cell_count_2 : («universe» 2).length = 71 := by decide +kernel
theorem initial_count_2 : (initial 2).length = 49 := by decide +kernel
theorem step_2_00 : stepCheck 2 (pairs2.take 0) (pairs2.getD 0 default) = true := by decide +kernel
theorem step_2_01 : stepCheck 2 (pairs2.take 1) (pairs2.getD 1 default) = true := by decide +kernel
theorem step_2_02 : stepCheck 2 (pairs2.take 2) (pairs2.getD 2 default) = true := by decide +kernel
theorem step_2_03 : stepCheck 2 (pairs2.take 3) (pairs2.getD 3 default) = true := by decide +kernel
theorem step_2_04 : stepCheck 2 (pairs2.take 4) (pairs2.getD 4 default) = true := by decide +kernel
theorem step_2_05 : stepCheck 2 (pairs2.take 5) (pairs2.getD 5 default) = true := by decide +kernel
theorem step_2_06 : stepCheck 2 (pairs2.take 6) (pairs2.getD 6 default) = true := by decide +kernel
theorem step_2_07 : stepCheck 2 (pairs2.take 7) (pairs2.getD 7 default) = true := by decide +kernel
theorem step_2_08 : stepCheck 2 (pairs2.take 8) (pairs2.getD 8 default) = true := by decide +kernel
theorem step_2_09 : stepCheck 2 (pairs2.take 9) (pairs2.getD 9 default) = true := by decide +kernel
theorem step_2_10 : stepCheck 2 (pairs2.take 10) (pairs2.getD 10 default) = true := by decide +kernel
theorem coverage_check_2 : coverageCheck 2 pairs2 = true := by decide +kernel
theorem rank_check_2 : rankCheck pairs2 = true := by decide +kernel

def pairs3 : List Pair := [
  ⟨[1, 7, 19], 0⟩,
  ⟨[1, 15, 19], 0⟩,
  ⟨[1, 3, 7, 19], 0⟩,
  ⟨[1, 3, 15, 19], 0⟩,
  ⟨[1, 3, 18, 19], 0⟩,
  ⟨[1, 5, 7, 19], 0⟩,
  ⟨[1, 5, 15, 19], 0⟩,
  ⟨[1, 7, 15, 19], 0⟩,
  ⟨[1, 7, 18, 19], 0⟩,
  ⟨[1, 9, 15, 19], 0⟩,
  ⟨[1, 11, 15, 19], 0⟩,
  ⟨[1, 13, 15, 19], 0⟩,
  ⟨[2, 3, 7, 19], 1⟩,
  ⟨[2, 3, 15, 19], 1⟩,
  ⟨[2, 6, 7, 19], 0⟩,
  ⟨[2, 6, 15, 19], 0⟩,
  ⟨[2, 10, 15, 19], 0⟩,
  ⟨[2, 14, 15, 19], 0⟩,
  ⟨[4, 5, 7, 19], 1⟩,
  ⟨[4, 5, 15, 19], 1⟩,
  ⟨[4, 12, 15, 19], 0⟩,
  ⟨[8, 9, 15, 19], 1⟩,
  ⟨[1, 3, 7, 15, 19], 0⟩,
  ⟨[1, 3, 7, 18, 19], 0⟩,
  ⟨[1, 3, 11, 15, 19], 0⟩,
  ⟨[1, 5, 7, 15, 19], 0⟩,
  ⟨[1, 5, 7, 18, 19], 0⟩,
  ⟨[1, 5, 13, 15, 19], 0⟩,
  ⟨[1, 9, 11, 15, 19], 0⟩,
  ⟨[1, 9, 13, 15, 19], 0⟩,
  ⟨[2, 3, 7, 15, 19], 1⟩,
  ⟨[2, 3, 11, 15, 19], 1⟩,
  ⟨[2, 6, 7, 15, 19], 0⟩,
  ⟨[2, 6, 14, 15, 19], 0⟩,
  ⟨[2, 10, 11, 15, 19], 0⟩,
  ⟨[2, 10, 14, 15, 19], 0⟩,
  ⟨[4, 5, 7, 15, 19], 1⟩,
  ⟨[4, 5, 7, 18, 19], 1⟩,
  ⟨[4, 5, 13, 15, 19], 1⟩,
  ⟨[4, 12, 13, 15, 19], 0⟩,
  ⟨[8, 9, 11, 15, 19], 1⟩,
  ⟨[8, 9, 13, 15, 19], 1⟩,
  ⟨[8, 10, 11, 15, 19], 2⟩,
  ⟨[8, 10, 14, 15, 19], 1⟩,
  ⟨[8, 12, 13, 15, 19], 2⟩,
  ⟨[8, 12, 14, 15, 19], 0⟩,
  ⟨[4, 12, 14, 15, 19], 1⟩,
  ⟨[4, 6, 14, 15, 19], 2⟩,
  ⟨[4, 6, 7, 15, 19], 3⟩,
  ⟨[4, 6, 7, 18, 19], 0⟩,
  ⟨[2, 6, 7, 18, 19], 1⟩,
  ⟨[2, 3, 7, 18, 19], 2⟩,
  ⟨[2, 3, 17, 18, 19], 0⟩,
  ⟨[1, 3, 17, 18, 19], 1⟩,
  ⟨[1, 16, 17, 18, 19], 0⟩]

theorem order_check_3 : orderCheck 3 = true := by decide +kernel

-- BEGIN CERTIFICATE04 PRIVATE DECOMPOSITION
private theorem cert04_all_cons (p : Cell → Bool) (a : Cell) (s : List Cell)
    (ha : p a = true) (hs : s.all p = true) : (a :: s).all p = true := by
  change (p a && s.all p) = true
  exact Bool.and_eq_true_iff.mpr ⟨ha, hs⟩

private theorem cert04_distinct_cons (a : Cell) (s : List Cell)
    (ha : !s.contains a = true) (hs : distinct s = true) : distinct (a :: s) = true := by
  change (!s.contains a && distinct s) = true
  exact Bool.and_eq_true_iff.mpr ⟨ha, hs⟩

private def cert04_U_391 : List Cell := []
private def cert04_U_390 : List Cell := [1, 3, 7, 15, 19] :: cert04_U_391
private def cert04_U_389 : List Cell := [1, 3, 7, 18, 19] :: cert04_U_390
private def cert04_U_388 : List Cell := [1, 3, 7, 19] :: cert04_U_389
private def cert04_U_387 : List Cell := [1, 3, 7, 18] :: cert04_U_388
private def cert04_U_386 : List Cell := [1, 3, 7, 15] :: cert04_U_387
private def cert04_U_385 : List Cell := [1, 3, 11, 15, 19] :: cert04_U_386
private def cert04_U_384 : List Cell := [1, 3, 11, 19] :: cert04_U_385
private def cert04_U_383 : List Cell := [1, 3, 11, 15] :: cert04_U_384
private def cert04_U_382 : List Cell := [1, 3, 15, 19] :: cert04_U_383
private def cert04_U_381 : List Cell := [1, 3, 17, 18, 19] :: cert04_U_382
private def cert04_U_380 : List Cell := [1, 3, 17, 19] :: cert04_U_381
private def cert04_U_379 : List Cell := [1, 3, 17, 18] :: cert04_U_380
private def cert04_U_378 : List Cell := [1, 3, 18, 19] :: cert04_U_379
private def cert04_U_377 : List Cell := [1, 3, 19] :: cert04_U_378
private def cert04_U_376 : List Cell := [1, 3, 18] :: cert04_U_377
private def cert04_U_375 : List Cell := [1, 3, 17] :: cert04_U_376
private def cert04_U_374 : List Cell := [1, 3, 15] :: cert04_U_375
private def cert04_U_373 : List Cell := [1, 3, 11] :: cert04_U_374
private def cert04_U_372 : List Cell := [1, 3, 7] :: cert04_U_373
private def cert04_U_371 : List Cell := [1, 5, 7, 15, 19] :: cert04_U_372
private def cert04_U_370 : List Cell := [1, 5, 7, 18, 19] :: cert04_U_371
private def cert04_U_369 : List Cell := [1, 5, 7, 19] :: cert04_U_370
private def cert04_U_368 : List Cell := [1, 5, 7, 18] :: cert04_U_369
private def cert04_U_367 : List Cell := [1, 5, 7, 15] :: cert04_U_368
private def cert04_U_366 : List Cell := [1, 5, 13, 15, 19] :: cert04_U_367
private def cert04_U_365 : List Cell := [1, 5, 13, 19] :: cert04_U_366
private def cert04_U_364 : List Cell := [1, 5, 13, 15] :: cert04_U_365
private def cert04_U_363 : List Cell := [1, 5, 15, 19] :: cert04_U_364
private def cert04_U_362 : List Cell := [1, 5, 18, 19] :: cert04_U_363
private def cert04_U_361 : List Cell := [1, 5, 19] :: cert04_U_362
private def cert04_U_360 : List Cell := [1, 5, 18] :: cert04_U_361
private def cert04_U_359 : List Cell := [1, 5, 15] :: cert04_U_360
private def cert04_U_358 : List Cell := [1, 5, 13] :: cert04_U_359
private def cert04_U_357 : List Cell := [1, 5, 7] :: cert04_U_358
private def cert04_U_356 : List Cell := [1, 7, 15, 19] :: cert04_U_357
private def cert04_U_355 : List Cell := [1, 7, 18, 19] :: cert04_U_356
private def cert04_U_354 : List Cell := [1, 7, 19] :: cert04_U_355
private def cert04_U_353 : List Cell := [1, 7, 18] :: cert04_U_354
private def cert04_U_352 : List Cell := [1, 7, 15] :: cert04_U_353
private def cert04_U_351 : List Cell := [1, 9, 11, 15, 19] :: cert04_U_352
private def cert04_U_350 : List Cell := [1, 9, 11, 19] :: cert04_U_351
private def cert04_U_349 : List Cell := [1, 9, 11, 15] :: cert04_U_350
private def cert04_U_348 : List Cell := [1, 9, 13, 15, 19] :: cert04_U_349
private def cert04_U_347 : List Cell := [1, 9, 13, 19] :: cert04_U_348
private def cert04_U_346 : List Cell := [1, 9, 13, 15] :: cert04_U_347
private def cert04_U_345 : List Cell := [1, 9, 15, 19] :: cert04_U_346
private def cert04_U_344 : List Cell := [1, 9, 19] :: cert04_U_345
private def cert04_U_343 : List Cell := [1, 9, 15] :: cert04_U_344
private def cert04_U_342 : List Cell := [1, 9, 13] :: cert04_U_343
private def cert04_U_341 : List Cell := [1, 9, 11] :: cert04_U_342
private def cert04_U_340 : List Cell := [1, 11, 15, 19] :: cert04_U_341
private def cert04_U_339 : List Cell := [1, 11, 19] :: cert04_U_340
private def cert04_U_338 : List Cell := [1, 11, 15] :: cert04_U_339
private def cert04_U_337 : List Cell := [1, 13, 15, 19] :: cert04_U_338
private def cert04_U_336 : List Cell := [1, 13, 19] :: cert04_U_337
private def cert04_U_335 : List Cell := [1, 13, 15] :: cert04_U_336
private def cert04_U_334 : List Cell := [1, 15, 19] :: cert04_U_335
private def cert04_U_333 : List Cell := [1, 16, 17, 18, 19] :: cert04_U_334
private def cert04_U_332 : List Cell := [1, 16, 17, 19] :: cert04_U_333
private def cert04_U_331 : List Cell := [1, 16, 17, 18] :: cert04_U_332
private def cert04_U_330 : List Cell := [1, 16, 18, 19] :: cert04_U_331
private def cert04_U_329 : List Cell := [1, 16, 19] :: cert04_U_330
private def cert04_U_328 : List Cell := [1, 16, 18] :: cert04_U_329
private def cert04_U_327 : List Cell := [1, 16, 17] :: cert04_U_328
private def cert04_U_326 : List Cell := [1, 17, 18, 19] :: cert04_U_327
private def cert04_U_325 : List Cell := [1, 17, 19] :: cert04_U_326
private def cert04_U_324 : List Cell := [1, 17, 18] :: cert04_U_325
private def cert04_U_323 : List Cell := [1, 18, 19] :: cert04_U_324
private def cert04_U_322 : List Cell := [1, 19] :: cert04_U_323
private def cert04_U_321 : List Cell := [1, 18] :: cert04_U_322
private def cert04_U_320 : List Cell := [1, 17] :: cert04_U_321
private def cert04_U_319 : List Cell := [1, 16] :: cert04_U_320
private def cert04_U_318 : List Cell := [1, 15] :: cert04_U_319
private def cert04_U_317 : List Cell := [1, 13] :: cert04_U_318
private def cert04_U_316 : List Cell := [1, 11] :: cert04_U_317
private def cert04_U_315 : List Cell := [1, 9] :: cert04_U_316
private def cert04_U_314 : List Cell := [1, 7] :: cert04_U_315
private def cert04_U_313 : List Cell := [1, 5] :: cert04_U_314
private def cert04_U_312 : List Cell := [1, 3] :: cert04_U_313
private def cert04_U_311 : List Cell := [2, 3, 7, 15, 19] :: cert04_U_312
private def cert04_U_310 : List Cell := [2, 3, 7, 18, 19] :: cert04_U_311
private def cert04_U_309 : List Cell := [2, 3, 7, 19] :: cert04_U_310
private def cert04_U_308 : List Cell := [2, 3, 7, 18] :: cert04_U_309
private def cert04_U_307 : List Cell := [2, 3, 7, 15] :: cert04_U_308
private def cert04_U_306 : List Cell := [2, 3, 11, 15, 19] :: cert04_U_307
private def cert04_U_305 : List Cell := [2, 3, 11, 19] :: cert04_U_306
private def cert04_U_304 : List Cell := [2, 3, 11, 15] :: cert04_U_305
private def cert04_U_303 : List Cell := [2, 3, 15, 19] :: cert04_U_304
private def cert04_U_302 : List Cell := [2, 3, 17, 18, 19] :: cert04_U_303
private def cert04_U_301 : List Cell := [2, 3, 17, 19] :: cert04_U_302
private def cert04_U_300 : List Cell := [2, 3, 17, 18] :: cert04_U_301
private def cert04_U_299 : List Cell := [2, 3, 18, 19] :: cert04_U_300
private def cert04_U_298 : List Cell := [2, 3, 19] :: cert04_U_299
private def cert04_U_297 : List Cell := [2, 3, 18] :: cert04_U_298
private def cert04_U_296 : List Cell := [2, 3, 17] :: cert04_U_297
private def cert04_U_295 : List Cell := [2, 3, 15] :: cert04_U_296
private def cert04_U_294 : List Cell := [2, 3, 11] :: cert04_U_295
private def cert04_U_293 : List Cell := [2, 3, 7] :: cert04_U_294
private def cert04_U_292 : List Cell := [2, 6, 7, 15, 19] :: cert04_U_293
private def cert04_U_291 : List Cell := [2, 6, 7, 18, 19] :: cert04_U_292
private def cert04_U_290 : List Cell := [2, 6, 7, 19] :: cert04_U_291
private def cert04_U_289 : List Cell := [2, 6, 7, 18] :: cert04_U_290
private def cert04_U_288 : List Cell := [2, 6, 7, 15] :: cert04_U_289
private def cert04_U_287 : List Cell := [2, 6, 14, 15, 19] :: cert04_U_288
private def cert04_U_286 : List Cell := [2, 6, 14, 19] :: cert04_U_287
private def cert04_U_285 : List Cell := [2, 6, 14, 15] :: cert04_U_286
private def cert04_U_284 : List Cell := [2, 6, 15, 19] :: cert04_U_285
private def cert04_U_283 : List Cell := [2, 6, 18, 19] :: cert04_U_284
private def cert04_U_282 : List Cell := [2, 6, 19] :: cert04_U_283
private def cert04_U_281 : List Cell := [2, 6, 18] :: cert04_U_282
private def cert04_U_280 : List Cell := [2, 6, 15] :: cert04_U_281
private def cert04_U_279 : List Cell := [2, 6, 14] :: cert04_U_280
private def cert04_U_278 : List Cell := [2, 6, 7] :: cert04_U_279
private def cert04_U_277 : List Cell := [2, 7, 15, 19] :: cert04_U_278
private def cert04_U_276 : List Cell := [2, 7, 18, 19] :: cert04_U_277
private def cert04_U_275 : List Cell := [2, 7, 19] :: cert04_U_276
private def cert04_U_274 : List Cell := [2, 7, 18] :: cert04_U_275
private def cert04_U_273 : List Cell := [2, 7, 15] :: cert04_U_274
private def cert04_U_272 : List Cell := [2, 10, 11, 15, 19] :: cert04_U_273
private def cert04_U_271 : List Cell := [2, 10, 11, 19] :: cert04_U_272
private def cert04_U_270 : List Cell := [2, 10, 11, 15] :: cert04_U_271
private def cert04_U_269 : List Cell := [2, 10, 14, 15, 19] :: cert04_U_270
private def cert04_U_268 : List Cell := [2, 10, 14, 19] :: cert04_U_269
private def cert04_U_267 : List Cell := [2, 10, 14, 15] :: cert04_U_268
private def cert04_U_266 : List Cell := [2, 10, 15, 19] :: cert04_U_267
private def cert04_U_265 : List Cell := [2, 10, 19] :: cert04_U_266
private def cert04_U_264 : List Cell := [2, 10, 15] :: cert04_U_265
private def cert04_U_263 : List Cell := [2, 10, 14] :: cert04_U_264
private def cert04_U_262 : List Cell := [2, 10, 11] :: cert04_U_263
private def cert04_U_261 : List Cell := [2, 11, 15, 19] :: cert04_U_262
private def cert04_U_260 : List Cell := [2, 11, 19] :: cert04_U_261
private def cert04_U_259 : List Cell := [2, 11, 15] :: cert04_U_260
private def cert04_U_258 : List Cell := [2, 14, 15, 19] :: cert04_U_259
private def cert04_U_257 : List Cell := [2, 14, 19] :: cert04_U_258
private def cert04_U_256 : List Cell := [2, 14, 15] :: cert04_U_257
private def cert04_U_255 : List Cell := [2, 15, 19] :: cert04_U_256
private def cert04_U_254 : List Cell := [2, 17, 18, 19] :: cert04_U_255
private def cert04_U_253 : List Cell := [2, 17, 19] :: cert04_U_254
private def cert04_U_252 : List Cell := [2, 17, 18] :: cert04_U_253
private def cert04_U_251 : List Cell := [2, 18, 19] :: cert04_U_252
private def cert04_U_250 : List Cell := [2, 19] :: cert04_U_251
private def cert04_U_249 : List Cell := [2, 18] :: cert04_U_250
private def cert04_U_248 : List Cell := [2, 17] :: cert04_U_249
private def cert04_U_247 : List Cell := [2, 15] :: cert04_U_248
private def cert04_U_246 : List Cell := [2, 14] :: cert04_U_247
private def cert04_U_245 : List Cell := [2, 11] :: cert04_U_246
private def cert04_U_244 : List Cell := [2, 10] :: cert04_U_245
private def cert04_U_243 : List Cell := [2, 7] :: cert04_U_244
private def cert04_U_242 : List Cell := [2, 6] :: cert04_U_243
private def cert04_U_241 : List Cell := [2, 3] :: cert04_U_242
private def cert04_U_240 : List Cell := [3, 7, 15, 19] :: cert04_U_241
private def cert04_U_239 : List Cell := [3, 7, 18, 19] :: cert04_U_240
private def cert04_U_238 : List Cell := [3, 7, 19] :: cert04_U_239
private def cert04_U_237 : List Cell := [3, 7, 18] :: cert04_U_238
private def cert04_U_236 : List Cell := [3, 7, 15] :: cert04_U_237
private def cert04_U_235 : List Cell := [3, 11, 15, 19] :: cert04_U_236
private def cert04_U_234 : List Cell := [3, 11, 19] :: cert04_U_235
private def cert04_U_233 : List Cell := [3, 11, 15] :: cert04_U_234
private def cert04_U_232 : List Cell := [3, 15, 19] :: cert04_U_233
private def cert04_U_231 : List Cell := [3, 17, 18, 19] :: cert04_U_232
private def cert04_U_230 : List Cell := [3, 17, 19] :: cert04_U_231
private def cert04_U_229 : List Cell := [3, 17, 18] :: cert04_U_230
private def cert04_U_228 : List Cell := [3, 18, 19] :: cert04_U_229
private def cert04_U_227 : List Cell := [3, 19] :: cert04_U_228
private def cert04_U_226 : List Cell := [3, 18] :: cert04_U_227
private def cert04_U_225 : List Cell := [3, 17] :: cert04_U_226
private def cert04_U_224 : List Cell := [3, 15] :: cert04_U_225
private def cert04_U_223 : List Cell := [3, 11] :: cert04_U_224
private def cert04_U_222 : List Cell := [3, 7] :: cert04_U_223
private def cert04_U_221 : List Cell := [4, 5, 7, 15, 19] :: cert04_U_222
private def cert04_U_220 : List Cell := [4, 5, 7, 18, 19] :: cert04_U_221
private def cert04_U_219 : List Cell := [4, 5, 7, 19] :: cert04_U_220
private def cert04_U_218 : List Cell := [4, 5, 7, 18] :: cert04_U_219
private def cert04_U_217 : List Cell := [4, 5, 7, 15] :: cert04_U_218
private def cert04_U_216 : List Cell := [4, 5, 13, 15, 19] :: cert04_U_217
private def cert04_U_215 : List Cell := [4, 5, 13, 19] :: cert04_U_216
private def cert04_U_214 : List Cell := [4, 5, 13, 15] :: cert04_U_215
private def cert04_U_213 : List Cell := [4, 5, 15, 19] :: cert04_U_214
private def cert04_U_212 : List Cell := [4, 5, 18, 19] :: cert04_U_213
private def cert04_U_211 : List Cell := [4, 5, 19] :: cert04_U_212
private def cert04_U_210 : List Cell := [4, 5, 18] :: cert04_U_211
private def cert04_U_209 : List Cell := [4, 5, 15] :: cert04_U_210
private def cert04_U_208 : List Cell := [4, 5, 13] :: cert04_U_209
private def cert04_U_207 : List Cell := [4, 5, 7] :: cert04_U_208
private def cert04_U_206 : List Cell := [4, 6, 7, 15, 19] :: cert04_U_207
private def cert04_U_205 : List Cell := [4, 6, 7, 18, 19] :: cert04_U_206
private def cert04_U_204 : List Cell := [4, 6, 7, 19] :: cert04_U_205
private def cert04_U_203 : List Cell := [4, 6, 7, 18] :: cert04_U_204
private def cert04_U_202 : List Cell := [4, 6, 7, 15] :: cert04_U_203
private def cert04_U_201 : List Cell := [4, 6, 14, 15, 19] :: cert04_U_202
private def cert04_U_200 : List Cell := [4, 6, 14, 19] :: cert04_U_201
private def cert04_U_199 : List Cell := [4, 6, 14, 15] :: cert04_U_200
private def cert04_U_198 : List Cell := [4, 6, 15, 19] :: cert04_U_199
private def cert04_U_197 : List Cell := [4, 6, 18, 19] :: cert04_U_198
private def cert04_U_196 : List Cell := [4, 6, 19] :: cert04_U_197
private def cert04_U_195 : List Cell := [4, 6, 18] :: cert04_U_196
private def cert04_U_194 : List Cell := [4, 6, 15] :: cert04_U_195
private def cert04_U_193 : List Cell := [4, 6, 14] :: cert04_U_194
private def cert04_U_192 : List Cell := [4, 6, 7] :: cert04_U_193
private def cert04_U_191 : List Cell := [4, 7, 15, 19] :: cert04_U_192
private def cert04_U_190 : List Cell := [4, 7, 18, 19] :: cert04_U_191
private def cert04_U_189 : List Cell := [4, 7, 19] :: cert04_U_190
private def cert04_U_188 : List Cell := [4, 7, 18] :: cert04_U_189
private def cert04_U_187 : List Cell := [4, 7, 15] :: cert04_U_188
private def cert04_U_186 : List Cell := [4, 12, 13, 15, 19] :: cert04_U_187
private def cert04_U_185 : List Cell := [4, 12, 13, 19] :: cert04_U_186
private def cert04_U_184 : List Cell := [4, 12, 13, 15] :: cert04_U_185
private def cert04_U_183 : List Cell := [4, 12, 14, 15, 19] :: cert04_U_184
private def cert04_U_182 : List Cell := [4, 12, 14, 19] :: cert04_U_183
private def cert04_U_181 : List Cell := [4, 12, 14, 15] :: cert04_U_182
private def cert04_U_180 : List Cell := [4, 12, 15, 19] :: cert04_U_181
private def cert04_U_179 : List Cell := [4, 12, 19] :: cert04_U_180
private def cert04_U_178 : List Cell := [4, 12, 15] :: cert04_U_179
private def cert04_U_177 : List Cell := [4, 12, 14] :: cert04_U_178
private def cert04_U_176 : List Cell := [4, 12, 13] :: cert04_U_177
private def cert04_U_175 : List Cell := [4, 13, 15, 19] :: cert04_U_176
private def cert04_U_174 : List Cell := [4, 13, 19] :: cert04_U_175
private def cert04_U_173 : List Cell := [4, 13, 15] :: cert04_U_174
private def cert04_U_172 : List Cell := [4, 14, 15, 19] :: cert04_U_173
private def cert04_U_171 : List Cell := [4, 14, 19] :: cert04_U_172
private def cert04_U_170 : List Cell := [4, 14, 15] :: cert04_U_171
private def cert04_U_169 : List Cell := [4, 15, 19] :: cert04_U_170
private def cert04_U_168 : List Cell := [4, 18, 19] :: cert04_U_169
private def cert04_U_167 : List Cell := [4, 19] :: cert04_U_168
private def cert04_U_166 : List Cell := [4, 18] :: cert04_U_167
private def cert04_U_165 : List Cell := [4, 15] :: cert04_U_166
private def cert04_U_164 : List Cell := [4, 14] :: cert04_U_165
private def cert04_U_163 : List Cell := [4, 13] :: cert04_U_164
private def cert04_U_162 : List Cell := [4, 12] :: cert04_U_163
private def cert04_U_161 : List Cell := [4, 7] :: cert04_U_162
private def cert04_U_160 : List Cell := [4, 6] :: cert04_U_161
private def cert04_U_159 : List Cell := [4, 5] :: cert04_U_160
private def cert04_U_158 : List Cell := [5, 7, 15, 19] :: cert04_U_159
private def cert04_U_157 : List Cell := [5, 7, 18, 19] :: cert04_U_158
private def cert04_U_156 : List Cell := [5, 7, 19] :: cert04_U_157
private def cert04_U_155 : List Cell := [5, 7, 18] :: cert04_U_156
private def cert04_U_154 : List Cell := [5, 7, 15] :: cert04_U_155
private def cert04_U_153 : List Cell := [5, 13, 15, 19] :: cert04_U_154
private def cert04_U_152 : List Cell := [5, 13, 19] :: cert04_U_153
private def cert04_U_151 : List Cell := [5, 13, 15] :: cert04_U_152
private def cert04_U_150 : List Cell := [5, 15, 19] :: cert04_U_151
private def cert04_U_149 : List Cell := [5, 18, 19] :: cert04_U_150
private def cert04_U_148 : List Cell := [5, 19] :: cert04_U_149
private def cert04_U_147 : List Cell := [5, 18] :: cert04_U_148
private def cert04_U_146 : List Cell := [5, 15] :: cert04_U_147
private def cert04_U_145 : List Cell := [5, 13] :: cert04_U_146
private def cert04_U_144 : List Cell := [5, 7] :: cert04_U_145
private def cert04_U_143 : List Cell := [6, 7, 15, 19] :: cert04_U_144
private def cert04_U_142 : List Cell := [6, 7, 18, 19] :: cert04_U_143
private def cert04_U_141 : List Cell := [6, 7, 19] :: cert04_U_142
private def cert04_U_140 : List Cell := [6, 7, 18] :: cert04_U_141
private def cert04_U_139 : List Cell := [6, 7, 15] :: cert04_U_140
private def cert04_U_138 : List Cell := [6, 14, 15, 19] :: cert04_U_139
private def cert04_U_137 : List Cell := [6, 14, 19] :: cert04_U_138
private def cert04_U_136 : List Cell := [6, 14, 15] :: cert04_U_137
private def cert04_U_135 : List Cell := [6, 15, 19] :: cert04_U_136
private def cert04_U_134 : List Cell := [6, 18, 19] :: cert04_U_135
private def cert04_U_133 : List Cell := [6, 19] :: cert04_U_134
private def cert04_U_132 : List Cell := [6, 18] :: cert04_U_133
private def cert04_U_131 : List Cell := [6, 15] :: cert04_U_132
private def cert04_U_130 : List Cell := [6, 14] :: cert04_U_131
private def cert04_U_129 : List Cell := [6, 7] :: cert04_U_130
private def cert04_U_128 : List Cell := [7, 15, 19] :: cert04_U_129
private def cert04_U_127 : List Cell := [7, 18, 19] :: cert04_U_128
private def cert04_U_126 : List Cell := [7, 19] :: cert04_U_127
private def cert04_U_125 : List Cell := [7, 18] :: cert04_U_126
private def cert04_U_124 : List Cell := [7, 15] :: cert04_U_125
private def cert04_U_123 : List Cell := [8, 9, 11, 15, 19] :: cert04_U_124
private def cert04_U_122 : List Cell := [8, 9, 11, 19] :: cert04_U_123
private def cert04_U_121 : List Cell := [8, 9, 11, 15] :: cert04_U_122
private def cert04_U_120 : List Cell := [8, 9, 13, 15, 19] :: cert04_U_121
private def cert04_U_119 : List Cell := [8, 9, 13, 19] :: cert04_U_120
private def cert04_U_118 : List Cell := [8, 9, 13, 15] :: cert04_U_119
private def cert04_U_117 : List Cell := [8, 9, 15, 19] :: cert04_U_118
private def cert04_U_116 : List Cell := [8, 9, 19] :: cert04_U_117
private def cert04_U_115 : List Cell := [8, 9, 15] :: cert04_U_116
private def cert04_U_114 : List Cell := [8, 9, 13] :: cert04_U_115
private def cert04_U_113 : List Cell := [8, 9, 11] :: cert04_U_114
private def cert04_U_112 : List Cell := [8, 10, 11, 15, 19] :: cert04_U_113
private def cert04_U_111 : List Cell := [8, 10, 11, 19] :: cert04_U_112
private def cert04_U_110 : List Cell := [8, 10, 11, 15] :: cert04_U_111
private def cert04_U_109 : List Cell := [8, 10, 14, 15, 19] :: cert04_U_110
private def cert04_U_108 : List Cell := [8, 10, 14, 19] :: cert04_U_109
private def cert04_U_107 : List Cell := [8, 10, 14, 15] :: cert04_U_108
private def cert04_U_106 : List Cell := [8, 10, 15, 19] :: cert04_U_107
private def cert04_U_105 : List Cell := [8, 10, 19] :: cert04_U_106
private def cert04_U_104 : List Cell := [8, 10, 15] :: cert04_U_105
private def cert04_U_103 : List Cell := [8, 10, 14] :: cert04_U_104
private def cert04_U_102 : List Cell := [8, 10, 11] :: cert04_U_103
private def cert04_U_101 : List Cell := [8, 11, 15, 19] :: cert04_U_102
private def cert04_U_100 : List Cell := [8, 11, 19] :: cert04_U_101
private def cert04_U_99 : List Cell := [8, 11, 15] :: cert04_U_100
private def cert04_U_98 : List Cell := [8, 12, 13, 15, 19] :: cert04_U_99
private def cert04_U_97 : List Cell := [8, 12, 13, 19] :: cert04_U_98
private def cert04_U_96 : List Cell := [8, 12, 13, 15] :: cert04_U_97
private def cert04_U_95 : List Cell := [8, 12, 14, 15, 19] :: cert04_U_96
private def cert04_U_94 : List Cell := [8, 12, 14, 19] :: cert04_U_95
private def cert04_U_93 : List Cell := [8, 12, 14, 15] :: cert04_U_94
private def cert04_U_92 : List Cell := [8, 12, 15, 19] :: cert04_U_93
private def cert04_U_91 : List Cell := [8, 12, 19] :: cert04_U_92
private def cert04_U_90 : List Cell := [8, 12, 15] :: cert04_U_91
private def cert04_U_89 : List Cell := [8, 12, 14] :: cert04_U_90
private def cert04_U_88 : List Cell := [8, 12, 13] :: cert04_U_89
private def cert04_U_87 : List Cell := [8, 13, 15, 19] :: cert04_U_88
private def cert04_U_86 : List Cell := [8, 13, 19] :: cert04_U_87
private def cert04_U_85 : List Cell := [8, 13, 15] :: cert04_U_86
private def cert04_U_84 : List Cell := [8, 14, 15, 19] :: cert04_U_85
private def cert04_U_83 : List Cell := [8, 14, 19] :: cert04_U_84
private def cert04_U_82 : List Cell := [8, 14, 15] :: cert04_U_83
private def cert04_U_81 : List Cell := [8, 15, 19] :: cert04_U_82
private def cert04_U_80 : List Cell := [8, 19] :: cert04_U_81
private def cert04_U_79 : List Cell := [8, 15] :: cert04_U_80
private def cert04_U_78 : List Cell := [8, 14] :: cert04_U_79
private def cert04_U_77 : List Cell := [8, 13] :: cert04_U_78
private def cert04_U_76 : List Cell := [8, 12] :: cert04_U_77
private def cert04_U_75 : List Cell := [8, 11] :: cert04_U_76
private def cert04_U_74 : List Cell := [8, 10] :: cert04_U_75
private def cert04_U_73 : List Cell := [8, 9] :: cert04_U_74
private def cert04_U_72 : List Cell := [9, 11, 15, 19] :: cert04_U_73
private def cert04_U_71 : List Cell := [9, 11, 19] :: cert04_U_72
private def cert04_U_70 : List Cell := [9, 11, 15] :: cert04_U_71
private def cert04_U_69 : List Cell := [9, 13, 15, 19] :: cert04_U_70
private def cert04_U_68 : List Cell := [9, 13, 19] :: cert04_U_69
private def cert04_U_67 : List Cell := [9, 13, 15] :: cert04_U_68
private def cert04_U_66 : List Cell := [9, 15, 19] :: cert04_U_67
private def cert04_U_65 : List Cell := [9, 19] :: cert04_U_66
private def cert04_U_64 : List Cell := [9, 15] :: cert04_U_65
private def cert04_U_63 : List Cell := [9, 13] :: cert04_U_64
private def cert04_U_62 : List Cell := [9, 11] :: cert04_U_63
private def cert04_U_61 : List Cell := [10, 11, 15, 19] :: cert04_U_62
private def cert04_U_60 : List Cell := [10, 11, 19] :: cert04_U_61
private def cert04_U_59 : List Cell := [10, 11, 15] :: cert04_U_60
private def cert04_U_58 : List Cell := [10, 14, 15, 19] :: cert04_U_59
private def cert04_U_57 : List Cell := [10, 14, 19] :: cert04_U_58
private def cert04_U_56 : List Cell := [10, 14, 15] :: cert04_U_57
private def cert04_U_55 : List Cell := [10, 15, 19] :: cert04_U_56
private def cert04_U_54 : List Cell := [10, 19] :: cert04_U_55
private def cert04_U_53 : List Cell := [10, 15] :: cert04_U_54
private def cert04_U_52 : List Cell := [10, 14] :: cert04_U_53
private def cert04_U_51 : List Cell := [10, 11] :: cert04_U_52
private def cert04_U_50 : List Cell := [11, 15, 19] :: cert04_U_51
private def cert04_U_49 : List Cell := [11, 19] :: cert04_U_50
private def cert04_U_48 : List Cell := [11, 15] :: cert04_U_49
private def cert04_U_47 : List Cell := [12, 13, 15, 19] :: cert04_U_48
private def cert04_U_46 : List Cell := [12, 13, 19] :: cert04_U_47
private def cert04_U_45 : List Cell := [12, 13, 15] :: cert04_U_46
private def cert04_U_44 : List Cell := [12, 14, 15, 19] :: cert04_U_45
private def cert04_U_43 : List Cell := [12, 14, 19] :: cert04_U_44
private def cert04_U_42 : List Cell := [12, 14, 15] :: cert04_U_43
private def cert04_U_41 : List Cell := [12, 15, 19] :: cert04_U_42
private def cert04_U_40 : List Cell := [12, 19] :: cert04_U_41
private def cert04_U_39 : List Cell := [12, 15] :: cert04_U_40
private def cert04_U_38 : List Cell := [12, 14] :: cert04_U_39
private def cert04_U_37 : List Cell := [12, 13] :: cert04_U_38
private def cert04_U_36 : List Cell := [13, 15, 19] :: cert04_U_37
private def cert04_U_35 : List Cell := [13, 19] :: cert04_U_36
private def cert04_U_34 : List Cell := [13, 15] :: cert04_U_35
private def cert04_U_33 : List Cell := [14, 15, 19] :: cert04_U_34
private def cert04_U_32 : List Cell := [14, 19] :: cert04_U_33
private def cert04_U_31 : List Cell := [14, 15] :: cert04_U_32
private def cert04_U_30 : List Cell := [15, 19] :: cert04_U_31
private def cert04_U_29 : List Cell := [16, 17, 18, 19] :: cert04_U_30
private def cert04_U_28 : List Cell := [16, 17, 19] :: cert04_U_29
private def cert04_U_27 : List Cell := [16, 17, 18] :: cert04_U_28
private def cert04_U_26 : List Cell := [16, 18, 19] :: cert04_U_27
private def cert04_U_25 : List Cell := [16, 19] :: cert04_U_26
private def cert04_U_24 : List Cell := [16, 18] :: cert04_U_25
private def cert04_U_23 : List Cell := [16, 17] :: cert04_U_24
private def cert04_U_22 : List Cell := [17, 18, 19] :: cert04_U_23
private def cert04_U_21 : List Cell := [17, 19] :: cert04_U_22
private def cert04_U_20 : List Cell := [17, 18] :: cert04_U_21
private def cert04_U_19 : List Cell := [18, 19] :: cert04_U_20
private def cert04_U_18 : List Cell := [19] :: cert04_U_19
private def cert04_U_17 : List Cell := [18] :: cert04_U_18
private def cert04_U_16 : List Cell := [17] :: cert04_U_17
private def cert04_U_15 : List Cell := [16] :: cert04_U_16
private def cert04_U_14 : List Cell := [15] :: cert04_U_15
private def cert04_U_13 : List Cell := [14] :: cert04_U_14
private def cert04_U_12 : List Cell := [13] :: cert04_U_13
private def cert04_U_11 : List Cell := [12] :: cert04_U_12
private def cert04_U_10 : List Cell := [11] :: cert04_U_11
private def cert04_U_9 : List Cell := [10] :: cert04_U_10
private def cert04_U_8 : List Cell := [9] :: cert04_U_9
private def cert04_U_7 : List Cell := [8] :: cert04_U_8
private def cert04_U_6 : List Cell := [7] :: cert04_U_7
private def cert04_U_5 : List Cell := [6] :: cert04_U_6
private def cert04_U_4 : List Cell := [5] :: cert04_U_5
private def cert04_U_3 : List Cell := [4] :: cert04_U_4
private def cert04_U_2 : List Cell := [3] :: cert04_U_3
private def cert04_U_1 : List Cell := [2] :: cert04_U_2
private def cert04_U_0 : List Cell := [1] :: cert04_U_1
private def cert04_I_281 : List Cell := []
private def cert04_I_280 : List Cell := [1, 3, 7, 18] :: cert04_I_281
private def cert04_I_279 : List Cell := [1, 3, 7, 15] :: cert04_I_280
private def cert04_I_278 : List Cell := [1, 3, 11, 19] :: cert04_I_279
private def cert04_I_277 : List Cell := [1, 3, 11, 15] :: cert04_I_278
private def cert04_I_276 : List Cell := [1, 3, 17, 19] :: cert04_I_277
private def cert04_I_275 : List Cell := [1, 3, 17, 18] :: cert04_I_276
private def cert04_I_274 : List Cell := [1, 3, 19] :: cert04_I_275
private def cert04_I_273 : List Cell := [1, 3, 18] :: cert04_I_274
private def cert04_I_272 : List Cell := [1, 3, 17] :: cert04_I_273
private def cert04_I_271 : List Cell := [1, 3, 15] :: cert04_I_272
private def cert04_I_270 : List Cell := [1, 3, 11] :: cert04_I_271
private def cert04_I_269 : List Cell := [1, 3, 7] :: cert04_I_270
private def cert04_I_268 : List Cell := [1, 5, 7, 18] :: cert04_I_269
private def cert04_I_267 : List Cell := [1, 5, 7, 15] :: cert04_I_268
private def cert04_I_266 : List Cell := [1, 5, 13, 19] :: cert04_I_267
private def cert04_I_265 : List Cell := [1, 5, 13, 15] :: cert04_I_266
private def cert04_I_264 : List Cell := [1, 5, 18, 19] :: cert04_I_265
private def cert04_I_263 : List Cell := [1, 5, 19] :: cert04_I_264
private def cert04_I_262 : List Cell := [1, 5, 18] :: cert04_I_263
private def cert04_I_261 : List Cell := [1, 5, 15] :: cert04_I_262
private def cert04_I_260 : List Cell := [1, 5, 13] :: cert04_I_261
private def cert04_I_259 : List Cell := [1, 5, 7] :: cert04_I_260
private def cert04_I_258 : List Cell := [1, 7, 18] :: cert04_I_259
private def cert04_I_257 : List Cell := [1, 7, 15] :: cert04_I_258
private def cert04_I_256 : List Cell := [1, 9, 11, 19] :: cert04_I_257
private def cert04_I_255 : List Cell := [1, 9, 11, 15] :: cert04_I_256
private def cert04_I_254 : List Cell := [1, 9, 13, 19] :: cert04_I_255
private def cert04_I_253 : List Cell := [1, 9, 13, 15] :: cert04_I_254
private def cert04_I_252 : List Cell := [1, 9, 19] :: cert04_I_253
private def cert04_I_251 : List Cell := [1, 9, 15] :: cert04_I_252
private def cert04_I_250 : List Cell := [1, 9, 13] :: cert04_I_251
private def cert04_I_249 : List Cell := [1, 9, 11] :: cert04_I_250
private def cert04_I_248 : List Cell := [1, 11, 19] :: cert04_I_249
private def cert04_I_247 : List Cell := [1, 11, 15] :: cert04_I_248
private def cert04_I_246 : List Cell := [1, 13, 19] :: cert04_I_247
private def cert04_I_245 : List Cell := [1, 13, 15] :: cert04_I_246
private def cert04_I_244 : List Cell := [1, 16, 17, 19] :: cert04_I_245
private def cert04_I_243 : List Cell := [1, 16, 17, 18] :: cert04_I_244
private def cert04_I_242 : List Cell := [1, 16, 18, 19] :: cert04_I_243
private def cert04_I_241 : List Cell := [1, 16, 19] :: cert04_I_242
private def cert04_I_240 : List Cell := [1, 16, 18] :: cert04_I_241
private def cert04_I_239 : List Cell := [1, 16, 17] :: cert04_I_240
private def cert04_I_238 : List Cell := [1, 17, 19] :: cert04_I_239
private def cert04_I_237 : List Cell := [1, 17, 18] :: cert04_I_238
private def cert04_I_236 : List Cell := [1, 18, 19] :: cert04_I_237
private def cert04_I_235 : List Cell := [1, 19] :: cert04_I_236
private def cert04_I_234 : List Cell := [1, 18] :: cert04_I_235
private def cert04_I_233 : List Cell := [1, 17] :: cert04_I_234
private def cert04_I_232 : List Cell := [1, 16] :: cert04_I_233
private def cert04_I_231 : List Cell := [1, 15] :: cert04_I_232
private def cert04_I_230 : List Cell := [1, 13] :: cert04_I_231
private def cert04_I_229 : List Cell := [1, 11] :: cert04_I_230
private def cert04_I_228 : List Cell := [1, 9] :: cert04_I_229
private def cert04_I_227 : List Cell := [1, 7] :: cert04_I_228
private def cert04_I_226 : List Cell := [1, 5] :: cert04_I_227
private def cert04_I_225 : List Cell := [1, 3] :: cert04_I_226
private def cert04_I_224 : List Cell := [2, 3, 7, 18] :: cert04_I_225
private def cert04_I_223 : List Cell := [2, 3, 7, 15] :: cert04_I_224
private def cert04_I_222 : List Cell := [2, 3, 11, 19] :: cert04_I_223
private def cert04_I_221 : List Cell := [2, 3, 11, 15] :: cert04_I_222
private def cert04_I_220 : List Cell := [2, 3, 17, 19] :: cert04_I_221
private def cert04_I_219 : List Cell := [2, 3, 17, 18] :: cert04_I_220
private def cert04_I_218 : List Cell := [2, 3, 19] :: cert04_I_219
private def cert04_I_217 : List Cell := [2, 3, 18] :: cert04_I_218
private def cert04_I_216 : List Cell := [2, 3, 17] :: cert04_I_217
private def cert04_I_215 : List Cell := [2, 3, 15] :: cert04_I_216
private def cert04_I_214 : List Cell := [2, 3, 11] :: cert04_I_215
private def cert04_I_213 : List Cell := [2, 3, 7] :: cert04_I_214
private def cert04_I_212 : List Cell := [2, 6, 7, 18] :: cert04_I_213
private def cert04_I_211 : List Cell := [2, 6, 7, 15] :: cert04_I_212
private def cert04_I_210 : List Cell := [2, 6, 14, 19] :: cert04_I_211
private def cert04_I_209 : List Cell := [2, 6, 14, 15] :: cert04_I_210
private def cert04_I_208 : List Cell := [2, 6, 18, 19] :: cert04_I_209
private def cert04_I_207 : List Cell := [2, 6, 19] :: cert04_I_208
private def cert04_I_206 : List Cell := [2, 6, 18] :: cert04_I_207
private def cert04_I_205 : List Cell := [2, 6, 15] :: cert04_I_206
private def cert04_I_204 : List Cell := [2, 6, 14] :: cert04_I_205
private def cert04_I_203 : List Cell := [2, 6, 7] :: cert04_I_204
private def cert04_I_202 : List Cell := [2, 7, 18] :: cert04_I_203
private def cert04_I_201 : List Cell := [2, 7, 15] :: cert04_I_202
private def cert04_I_200 : List Cell := [2, 10, 11, 19] :: cert04_I_201
private def cert04_I_199 : List Cell := [2, 10, 11, 15] :: cert04_I_200
private def cert04_I_198 : List Cell := [2, 10, 14, 19] :: cert04_I_199
private def cert04_I_197 : List Cell := [2, 10, 14, 15] :: cert04_I_198
private def cert04_I_196 : List Cell := [2, 10, 19] :: cert04_I_197
private def cert04_I_195 : List Cell := [2, 10, 15] :: cert04_I_196
private def cert04_I_194 : List Cell := [2, 10, 14] :: cert04_I_195
private def cert04_I_193 : List Cell := [2, 10, 11] :: cert04_I_194
private def cert04_I_192 : List Cell := [2, 11, 19] :: cert04_I_193
private def cert04_I_191 : List Cell := [2, 11, 15] :: cert04_I_192
private def cert04_I_190 : List Cell := [2, 14, 19] :: cert04_I_191
private def cert04_I_189 : List Cell := [2, 14, 15] :: cert04_I_190
private def cert04_I_188 : List Cell := [2, 17, 18, 19] :: cert04_I_189
private def cert04_I_187 : List Cell := [2, 17, 19] :: cert04_I_188
private def cert04_I_186 : List Cell := [2, 17, 18] :: cert04_I_187
private def cert04_I_185 : List Cell := [2, 18, 19] :: cert04_I_186
private def cert04_I_184 : List Cell := [2, 19] :: cert04_I_185
private def cert04_I_183 : List Cell := [2, 18] :: cert04_I_184
private def cert04_I_182 : List Cell := [2, 17] :: cert04_I_183
private def cert04_I_181 : List Cell := [2, 15] :: cert04_I_182
private def cert04_I_180 : List Cell := [2, 14] :: cert04_I_181
private def cert04_I_179 : List Cell := [2, 11] :: cert04_I_180
private def cert04_I_178 : List Cell := [2, 10] :: cert04_I_179
private def cert04_I_177 : List Cell := [2, 7] :: cert04_I_178
private def cert04_I_176 : List Cell := [2, 6] :: cert04_I_177
private def cert04_I_175 : List Cell := [2, 3] :: cert04_I_176
private def cert04_I_174 : List Cell := [3, 7, 18] :: cert04_I_175
private def cert04_I_173 : List Cell := [3, 7, 15] :: cert04_I_174
private def cert04_I_172 : List Cell := [3, 11, 19] :: cert04_I_173
private def cert04_I_171 : List Cell := [3, 11, 15] :: cert04_I_172
private def cert04_I_170 : List Cell := [3, 17, 19] :: cert04_I_171
private def cert04_I_169 : List Cell := [3, 17, 18] :: cert04_I_170
private def cert04_I_168 : List Cell := [3, 19] :: cert04_I_169
private def cert04_I_167 : List Cell := [3, 18] :: cert04_I_168
private def cert04_I_166 : List Cell := [3, 17] :: cert04_I_167
private def cert04_I_165 : List Cell := [3, 15] :: cert04_I_166
private def cert04_I_164 : List Cell := [3, 11] :: cert04_I_165
private def cert04_I_163 : List Cell := [3, 7] :: cert04_I_164
private def cert04_I_162 : List Cell := [4, 5, 7, 18] :: cert04_I_163
private def cert04_I_161 : List Cell := [4, 5, 7, 15] :: cert04_I_162
private def cert04_I_160 : List Cell := [4, 5, 13, 19] :: cert04_I_161
private def cert04_I_159 : List Cell := [4, 5, 13, 15] :: cert04_I_160
private def cert04_I_158 : List Cell := [4, 5, 18, 19] :: cert04_I_159
private def cert04_I_157 : List Cell := [4, 5, 19] :: cert04_I_158
private def cert04_I_156 : List Cell := [4, 5, 18] :: cert04_I_157
private def cert04_I_155 : List Cell := [4, 5, 15] :: cert04_I_156
private def cert04_I_154 : List Cell := [4, 5, 13] :: cert04_I_155
private def cert04_I_153 : List Cell := [4, 5, 7] :: cert04_I_154
private def cert04_I_152 : List Cell := [4, 6, 7, 18] :: cert04_I_153
private def cert04_I_151 : List Cell := [4, 6, 7, 15] :: cert04_I_152
private def cert04_I_150 : List Cell := [4, 6, 14, 19] :: cert04_I_151
private def cert04_I_149 : List Cell := [4, 6, 14, 15] :: cert04_I_150
private def cert04_I_148 : List Cell := [4, 6, 18, 19] :: cert04_I_149
private def cert04_I_147 : List Cell := [4, 6, 19] :: cert04_I_148
private def cert04_I_146 : List Cell := [4, 6, 18] :: cert04_I_147
private def cert04_I_145 : List Cell := [4, 6, 15] :: cert04_I_146
private def cert04_I_144 : List Cell := [4, 6, 14] :: cert04_I_145
private def cert04_I_143 : List Cell := [4, 6, 7] :: cert04_I_144
private def cert04_I_142 : List Cell := [4, 7, 18] :: cert04_I_143
private def cert04_I_141 : List Cell := [4, 7, 15] :: cert04_I_142
private def cert04_I_140 : List Cell := [4, 12, 13, 19] :: cert04_I_141
private def cert04_I_139 : List Cell := [4, 12, 13, 15] :: cert04_I_140
private def cert04_I_138 : List Cell := [4, 12, 14, 19] :: cert04_I_139
private def cert04_I_137 : List Cell := [4, 12, 14, 15] :: cert04_I_138
private def cert04_I_136 : List Cell := [4, 12, 19] :: cert04_I_137
private def cert04_I_135 : List Cell := [4, 12, 15] :: cert04_I_136
private def cert04_I_134 : List Cell := [4, 12, 14] :: cert04_I_135
private def cert04_I_133 : List Cell := [4, 12, 13] :: cert04_I_134
private def cert04_I_132 : List Cell := [4, 13, 19] :: cert04_I_133
private def cert04_I_131 : List Cell := [4, 13, 15] :: cert04_I_132
private def cert04_I_130 : List Cell := [4, 14, 19] :: cert04_I_131
private def cert04_I_129 : List Cell := [4, 14, 15] :: cert04_I_130
private def cert04_I_128 : List Cell := [4, 18, 19] :: cert04_I_129
private def cert04_I_127 : List Cell := [4, 19] :: cert04_I_128
private def cert04_I_126 : List Cell := [4, 18] :: cert04_I_127
private def cert04_I_125 : List Cell := [4, 15] :: cert04_I_126
private def cert04_I_124 : List Cell := [4, 14] :: cert04_I_125
private def cert04_I_123 : List Cell := [4, 13] :: cert04_I_124
private def cert04_I_122 : List Cell := [4, 12] :: cert04_I_123
private def cert04_I_121 : List Cell := [4, 7] :: cert04_I_122
private def cert04_I_120 : List Cell := [4, 6] :: cert04_I_121
private def cert04_I_119 : List Cell := [4, 5] :: cert04_I_120
private def cert04_I_118 : List Cell := [5, 7, 18] :: cert04_I_119
private def cert04_I_117 : List Cell := [5, 7, 15] :: cert04_I_118
private def cert04_I_116 : List Cell := [5, 13, 19] :: cert04_I_117
private def cert04_I_115 : List Cell := [5, 13, 15] :: cert04_I_116
private def cert04_I_114 : List Cell := [5, 18, 19] :: cert04_I_115
private def cert04_I_113 : List Cell := [5, 19] :: cert04_I_114
private def cert04_I_112 : List Cell := [5, 18] :: cert04_I_113
private def cert04_I_111 : List Cell := [5, 15] :: cert04_I_112
private def cert04_I_110 : List Cell := [5, 13] :: cert04_I_111
private def cert04_I_109 : List Cell := [5, 7] :: cert04_I_110
private def cert04_I_108 : List Cell := [6, 7, 18] :: cert04_I_109
private def cert04_I_107 : List Cell := [6, 7, 15] :: cert04_I_108
private def cert04_I_106 : List Cell := [6, 14, 19] :: cert04_I_107
private def cert04_I_105 : List Cell := [6, 14, 15] :: cert04_I_106
private def cert04_I_104 : List Cell := [6, 18, 19] :: cert04_I_105
private def cert04_I_103 : List Cell := [6, 19] :: cert04_I_104
private def cert04_I_102 : List Cell := [6, 18] :: cert04_I_103
private def cert04_I_101 : List Cell := [6, 15] :: cert04_I_102
private def cert04_I_100 : List Cell := [6, 14] :: cert04_I_101
private def cert04_I_99 : List Cell := [6, 7] :: cert04_I_100
private def cert04_I_98 : List Cell := [7, 18] :: cert04_I_99
private def cert04_I_97 : List Cell := [7, 15] :: cert04_I_98
private def cert04_I_96 : List Cell := [8, 9, 11, 19] :: cert04_I_97
private def cert04_I_95 : List Cell := [8, 9, 11, 15] :: cert04_I_96
private def cert04_I_94 : List Cell := [8, 9, 13, 19] :: cert04_I_95
private def cert04_I_93 : List Cell := [8, 9, 13, 15] :: cert04_I_94
private def cert04_I_92 : List Cell := [8, 9, 19] :: cert04_I_93
private def cert04_I_91 : List Cell := [8, 9, 15] :: cert04_I_92
private def cert04_I_90 : List Cell := [8, 9, 13] :: cert04_I_91
private def cert04_I_89 : List Cell := [8, 9, 11] :: cert04_I_90
private def cert04_I_88 : List Cell := [8, 10, 11, 19] :: cert04_I_89
private def cert04_I_87 : List Cell := [8, 10, 11, 15] :: cert04_I_88
private def cert04_I_86 : List Cell := [8, 10, 14, 19] :: cert04_I_87
private def cert04_I_85 : List Cell := [8, 10, 14, 15] :: cert04_I_86
private def cert04_I_84 : List Cell := [8, 10, 19] :: cert04_I_85
private def cert04_I_83 : List Cell := [8, 10, 15] :: cert04_I_84
private def cert04_I_82 : List Cell := [8, 10, 14] :: cert04_I_83
private def cert04_I_81 : List Cell := [8, 10, 11] :: cert04_I_82
private def cert04_I_80 : List Cell := [8, 11, 19] :: cert04_I_81
private def cert04_I_79 : List Cell := [8, 11, 15] :: cert04_I_80
private def cert04_I_78 : List Cell := [8, 12, 13, 19] :: cert04_I_79
private def cert04_I_77 : List Cell := [8, 12, 13, 15] :: cert04_I_78
private def cert04_I_76 : List Cell := [8, 12, 14, 19] :: cert04_I_77
private def cert04_I_75 : List Cell := [8, 12, 14, 15] :: cert04_I_76
private def cert04_I_74 : List Cell := [8, 12, 19] :: cert04_I_75
private def cert04_I_73 : List Cell := [8, 12, 15] :: cert04_I_74
private def cert04_I_72 : List Cell := [8, 12, 14] :: cert04_I_73
private def cert04_I_71 : List Cell := [8, 12, 13] :: cert04_I_72
private def cert04_I_70 : List Cell := [8, 13, 19] :: cert04_I_71
private def cert04_I_69 : List Cell := [8, 13, 15] :: cert04_I_70
private def cert04_I_68 : List Cell := [8, 14, 19] :: cert04_I_69
private def cert04_I_67 : List Cell := [8, 14, 15] :: cert04_I_68
private def cert04_I_66 : List Cell := [8, 19] :: cert04_I_67
private def cert04_I_65 : List Cell := [8, 15] :: cert04_I_66
private def cert04_I_64 : List Cell := [8, 14] :: cert04_I_65
private def cert04_I_63 : List Cell := [8, 13] :: cert04_I_64
private def cert04_I_62 : List Cell := [8, 12] :: cert04_I_63
private def cert04_I_61 : List Cell := [8, 11] :: cert04_I_62
private def cert04_I_60 : List Cell := [8, 10] :: cert04_I_61
private def cert04_I_59 : List Cell := [8, 9] :: cert04_I_60
private def cert04_I_58 : List Cell := [9, 11, 19] :: cert04_I_59
private def cert04_I_57 : List Cell := [9, 11, 15] :: cert04_I_58
private def cert04_I_56 : List Cell := [9, 13, 19] :: cert04_I_57
private def cert04_I_55 : List Cell := [9, 13, 15] :: cert04_I_56
private def cert04_I_54 : List Cell := [9, 19] :: cert04_I_55
private def cert04_I_53 : List Cell := [9, 15] :: cert04_I_54
private def cert04_I_52 : List Cell := [9, 13] :: cert04_I_53
private def cert04_I_51 : List Cell := [9, 11] :: cert04_I_52
private def cert04_I_50 : List Cell := [10, 11, 19] :: cert04_I_51
private def cert04_I_49 : List Cell := [10, 11, 15] :: cert04_I_50
private def cert04_I_48 : List Cell := [10, 14, 19] :: cert04_I_49
private def cert04_I_47 : List Cell := [10, 14, 15] :: cert04_I_48
private def cert04_I_46 : List Cell := [10, 19] :: cert04_I_47
private def cert04_I_45 : List Cell := [10, 15] :: cert04_I_46
private def cert04_I_44 : List Cell := [10, 14] :: cert04_I_45
private def cert04_I_43 : List Cell := [10, 11] :: cert04_I_44
private def cert04_I_42 : List Cell := [11, 19] :: cert04_I_43
private def cert04_I_41 : List Cell := [11, 15] :: cert04_I_42
private def cert04_I_40 : List Cell := [12, 13, 19] :: cert04_I_41
private def cert04_I_39 : List Cell := [12, 13, 15] :: cert04_I_40
private def cert04_I_38 : List Cell := [12, 14, 19] :: cert04_I_39
private def cert04_I_37 : List Cell := [12, 14, 15] :: cert04_I_38
private def cert04_I_36 : List Cell := [12, 19] :: cert04_I_37
private def cert04_I_35 : List Cell := [12, 15] :: cert04_I_36
private def cert04_I_34 : List Cell := [12, 14] :: cert04_I_35
private def cert04_I_33 : List Cell := [12, 13] :: cert04_I_34
private def cert04_I_32 : List Cell := [13, 19] :: cert04_I_33
private def cert04_I_31 : List Cell := [13, 15] :: cert04_I_32
private def cert04_I_30 : List Cell := [14, 19] :: cert04_I_31
private def cert04_I_29 : List Cell := [14, 15] :: cert04_I_30
private def cert04_I_28 : List Cell := [16, 17, 19] :: cert04_I_29
private def cert04_I_27 : List Cell := [16, 17, 18] :: cert04_I_28
private def cert04_I_26 : List Cell := [16, 18, 19] :: cert04_I_27
private def cert04_I_25 : List Cell := [16, 19] :: cert04_I_26
private def cert04_I_24 : List Cell := [16, 18] :: cert04_I_25
private def cert04_I_23 : List Cell := [16, 17] :: cert04_I_24
private def cert04_I_22 : List Cell := [17, 18, 19] :: cert04_I_23
private def cert04_I_21 : List Cell := [17, 19] :: cert04_I_22
private def cert04_I_20 : List Cell := [17, 18] :: cert04_I_21
private def cert04_I_19 : List Cell := [18, 19] :: cert04_I_20
private def cert04_I_18 : List Cell := [19] :: cert04_I_19
private def cert04_I_17 : List Cell := [18] :: cert04_I_18
private def cert04_I_16 : List Cell := [17] :: cert04_I_17
private def cert04_I_15 : List Cell := [16] :: cert04_I_16
private def cert04_I_14 : List Cell := [15] :: cert04_I_15
private def cert04_I_13 : List Cell := [14] :: cert04_I_14
private def cert04_I_12 : List Cell := [13] :: cert04_I_13
private def cert04_I_11 : List Cell := [12] :: cert04_I_12
private def cert04_I_10 : List Cell := [11] :: cert04_I_11
private def cert04_I_9 : List Cell := [10] :: cert04_I_10
private def cert04_I_8 : List Cell := [9] :: cert04_I_9
private def cert04_I_7 : List Cell := [8] :: cert04_I_8
private def cert04_I_6 : List Cell := [7] :: cert04_I_7
private def cert04_I_5 : List Cell := [6] :: cert04_I_6
private def cert04_I_4 : List Cell := [5] :: cert04_I_5
private def cert04_I_3 : List Cell := [4] :: cert04_I_4
private def cert04_I_2 : List Cell := [3] :: cert04_I_3
private def cert04_I_1 : List Cell := [2] :: cert04_I_2
private def cert04_I_0 : List Cell := [1] :: cert04_I_1
private def cert04_L_391 : List Cell := []
private def cert04_L_390 : List Cell := [16, 17, 18, 19] :: cert04_L_391
private def cert04_L_389 : List Cell := [1, 16, 17, 18, 19] :: cert04_L_390
private def cert04_L_388 : List Cell := [1, 17, 18, 19] :: cert04_L_389
private def cert04_L_387 : List Cell := [1, 3, 17, 18, 19] :: cert04_L_388
private def cert04_L_386 : List Cell := [3, 17, 18, 19] :: cert04_L_387
private def cert04_L_385 : List Cell := [2, 3, 17, 18, 19] :: cert04_L_386
private def cert04_L_384 : List Cell := [2, 3, 18, 19] :: cert04_L_385
private def cert04_L_383 : List Cell := [2, 3, 7, 18, 19] :: cert04_L_384
private def cert04_L_382 : List Cell := [2, 7, 18, 19] :: cert04_L_383
private def cert04_L_381 : List Cell := [2, 6, 7, 18, 19] :: cert04_L_382
private def cert04_L_380 : List Cell := [6, 7, 18, 19] :: cert04_L_381
private def cert04_L_379 : List Cell := [4, 6, 7, 18, 19] :: cert04_L_380
private def cert04_L_378 : List Cell := [4, 6, 7, 19] :: cert04_L_379
private def cert04_L_377 : List Cell := [4, 6, 7, 15, 19] :: cert04_L_378
private def cert04_L_376 : List Cell := [4, 6, 15, 19] :: cert04_L_377
private def cert04_L_375 : List Cell := [4, 6, 14, 15, 19] :: cert04_L_376
private def cert04_L_374 : List Cell := [4, 14, 15, 19] :: cert04_L_375
private def cert04_L_373 : List Cell := [4, 12, 14, 15, 19] :: cert04_L_374
private def cert04_L_372 : List Cell := [12, 14, 15, 19] :: cert04_L_373
private def cert04_L_371 : List Cell := [8, 12, 14, 15, 19] :: cert04_L_372
private def cert04_L_370 : List Cell := [8, 12, 15, 19] :: cert04_L_371
private def cert04_L_369 : List Cell := [8, 12, 13, 15, 19] :: cert04_L_370
private def cert04_L_368 : List Cell := [8, 14, 15, 19] :: cert04_L_369
private def cert04_L_367 : List Cell := [8, 10, 14, 15, 19] :: cert04_L_368
private def cert04_L_366 : List Cell := [8, 10, 15, 19] :: cert04_L_367
private def cert04_L_365 : List Cell := [8, 10, 11, 15, 19] :: cert04_L_366
private def cert04_L_364 : List Cell := [8, 13, 15, 19] :: cert04_L_365
private def cert04_L_363 : List Cell := [8, 9, 13, 15, 19] :: cert04_L_364
private def cert04_L_362 : List Cell := [8, 11, 15, 19] :: cert04_L_363
private def cert04_L_361 : List Cell := [8, 9, 11, 15, 19] :: cert04_L_362
private def cert04_L_360 : List Cell := [12, 13, 15, 19] :: cert04_L_361
private def cert04_L_359 : List Cell := [4, 12, 13, 15, 19] :: cert04_L_360
private def cert04_L_358 : List Cell := [4, 13, 15, 19] :: cert04_L_359
private def cert04_L_357 : List Cell := [4, 5, 13, 15, 19] :: cert04_L_358
private def cert04_L_356 : List Cell := [4, 7, 18, 19] :: cert04_L_357
private def cert04_L_355 : List Cell := [4, 5, 7, 18, 19] :: cert04_L_356
private def cert04_L_354 : List Cell := [4, 7, 15, 19] :: cert04_L_355
private def cert04_L_353 : List Cell := [4, 5, 7, 15, 19] :: cert04_L_354
private def cert04_L_352 : List Cell := [10, 14, 15, 19] :: cert04_L_353
private def cert04_L_351 : List Cell := [2, 10, 14, 15, 19] :: cert04_L_352
private def cert04_L_350 : List Cell := [10, 11, 15, 19] :: cert04_L_351
private def cert04_L_349 : List Cell := [2, 10, 11, 15, 19] :: cert04_L_350
private def cert04_L_348 : List Cell := [6, 14, 15, 19] :: cert04_L_349
private def cert04_L_347 : List Cell := [2, 6, 14, 15, 19] :: cert04_L_348
private def cert04_L_346 : List Cell := [6, 7, 15, 19] :: cert04_L_347
private def cert04_L_345 : List Cell := [2, 6, 7, 15, 19] :: cert04_L_346
private def cert04_L_344 : List Cell := [2, 11, 15, 19] :: cert04_L_345
private def cert04_L_343 : List Cell := [2, 3, 11, 15, 19] :: cert04_L_344
private def cert04_L_342 : List Cell := [2, 7, 15, 19] :: cert04_L_343
private def cert04_L_341 : List Cell := [2, 3, 7, 15, 19] :: cert04_L_342
private def cert04_L_340 : List Cell := [9, 13, 15, 19] :: cert04_L_341
private def cert04_L_339 : List Cell := [1, 9, 13, 15, 19] :: cert04_L_340
private def cert04_L_338 : List Cell := [9, 11, 15, 19] :: cert04_L_339
private def cert04_L_337 : List Cell := [1, 9, 11, 15, 19] :: cert04_L_338
private def cert04_L_336 : List Cell := [5, 13, 15, 19] :: cert04_L_337
private def cert04_L_335 : List Cell := [1, 5, 13, 15, 19] :: cert04_L_336
private def cert04_L_334 : List Cell := [5, 7, 18, 19] :: cert04_L_335
private def cert04_L_333 : List Cell := [1, 5, 7, 18, 19] :: cert04_L_334
private def cert04_L_332 : List Cell := [5, 7, 15, 19] :: cert04_L_333
private def cert04_L_331 : List Cell := [1, 5, 7, 15, 19] :: cert04_L_332
private def cert04_L_330 : List Cell := [3, 11, 15, 19] :: cert04_L_331
private def cert04_L_329 : List Cell := [1, 3, 11, 15, 19] :: cert04_L_330
private def cert04_L_328 : List Cell := [3, 7, 18, 19] :: cert04_L_329
private def cert04_L_327 : List Cell := [1, 3, 7, 18, 19] :: cert04_L_328
private def cert04_L_326 : List Cell := [3, 7, 15, 19] :: cert04_L_327
private def cert04_L_325 : List Cell := [1, 3, 7, 15, 19] :: cert04_L_326
private def cert04_L_324 : List Cell := [8, 15, 19] :: cert04_L_325
private def cert04_L_323 : List Cell := [8, 9, 15, 19] :: cert04_L_324
private def cert04_L_322 : List Cell := [12, 15, 19] :: cert04_L_323
private def cert04_L_321 : List Cell := [4, 12, 15, 19] :: cert04_L_322
private def cert04_L_320 : List Cell := [4, 15, 19] :: cert04_L_321
private def cert04_L_319 : List Cell := [4, 5, 15, 19] :: cert04_L_320
private def cert04_L_318 : List Cell := [4, 7, 19] :: cert04_L_319
private def cert04_L_317 : List Cell := [4, 5, 7, 19] :: cert04_L_318
private def cert04_L_316 : List Cell := [14, 15, 19] :: cert04_L_317
private def cert04_L_315 : List Cell := [2, 14, 15, 19] :: cert04_L_316
private def cert04_L_314 : List Cell := [10, 15, 19] :: cert04_L_315
private def cert04_L_313 : List Cell := [2, 10, 15, 19] :: cert04_L_314
private def cert04_L_312 : List Cell := [6, 15, 19] :: cert04_L_313
private def cert04_L_311 : List Cell := [2, 6, 15, 19] :: cert04_L_312
private def cert04_L_310 : List Cell := [6, 7, 19] :: cert04_L_311
private def cert04_L_309 : List Cell := [2, 6, 7, 19] :: cert04_L_310
private def cert04_L_308 : List Cell := [2, 15, 19] :: cert04_L_309
private def cert04_L_307 : List Cell := [2, 3, 15, 19] :: cert04_L_308
private def cert04_L_306 : List Cell := [2, 7, 19] :: cert04_L_307
private def cert04_L_305 : List Cell := [2, 3, 7, 19] :: cert04_L_306
private def cert04_L_304 : List Cell := [13, 15, 19] :: cert04_L_305
private def cert04_L_303 : List Cell := [1, 13, 15, 19] :: cert04_L_304
private def cert04_L_302 : List Cell := [11, 15, 19] :: cert04_L_303
private def cert04_L_301 : List Cell := [1, 11, 15, 19] :: cert04_L_302
private def cert04_L_300 : List Cell := [9, 15, 19] :: cert04_L_301
private def cert04_L_299 : List Cell := [1, 9, 15, 19] :: cert04_L_300
private def cert04_L_298 : List Cell := [7, 18, 19] :: cert04_L_299
private def cert04_L_297 : List Cell := [1, 7, 18, 19] :: cert04_L_298
private def cert04_L_296 : List Cell := [7, 15, 19] :: cert04_L_297
private def cert04_L_295 : List Cell := [1, 7, 15, 19] :: cert04_L_296
private def cert04_L_294 : List Cell := [5, 15, 19] :: cert04_L_295
private def cert04_L_293 : List Cell := [1, 5, 15, 19] :: cert04_L_294
private def cert04_L_292 : List Cell := [5, 7, 19] :: cert04_L_293
private def cert04_L_291 : List Cell := [1, 5, 7, 19] :: cert04_L_292
private def cert04_L_290 : List Cell := [3, 18, 19] :: cert04_L_291
private def cert04_L_289 : List Cell := [1, 3, 18, 19] :: cert04_L_290
private def cert04_L_288 : List Cell := [3, 15, 19] :: cert04_L_289
private def cert04_L_287 : List Cell := [1, 3, 15, 19] :: cert04_L_288
private def cert04_L_286 : List Cell := [3, 7, 19] :: cert04_L_287
private def cert04_L_285 : List Cell := [1, 3, 7, 19] :: cert04_L_286
private def cert04_L_284 : List Cell := [15, 19] :: cert04_L_285
private def cert04_L_283 : List Cell := [1, 15, 19] :: cert04_L_284
private def cert04_L_282 : List Cell := [7, 19] :: cert04_L_283
private def cert04_L_281 : List Cell := [1, 7, 19] :: cert04_L_282
private def cert04_L_280 : List Cell := [1, 3, 7, 18] :: cert04_L_281
private def cert04_L_279 : List Cell := [1, 3, 7, 15] :: cert04_L_280
private def cert04_L_278 : List Cell := [1, 3, 11, 19] :: cert04_L_279
private def cert04_L_277 : List Cell := [1, 3, 11, 15] :: cert04_L_278
private def cert04_L_276 : List Cell := [1, 3, 17, 19] :: cert04_L_277
private def cert04_L_275 : List Cell := [1, 3, 17, 18] :: cert04_L_276
private def cert04_L_274 : List Cell := [1, 3, 19] :: cert04_L_275
private def cert04_L_273 : List Cell := [1, 3, 18] :: cert04_L_274
private def cert04_L_272 : List Cell := [1, 3, 17] :: cert04_L_273
private def cert04_L_271 : List Cell := [1, 3, 15] :: cert04_L_272
private def cert04_L_270 : List Cell := [1, 3, 11] :: cert04_L_271
private def cert04_L_269 : List Cell := [1, 3, 7] :: cert04_L_270
private def cert04_L_268 : List Cell := [1, 5, 7, 18] :: cert04_L_269
private def cert04_L_267 : List Cell := [1, 5, 7, 15] :: cert04_L_268
private def cert04_L_266 : List Cell := [1, 5, 13, 19] :: cert04_L_267
private def cert04_L_265 : List Cell := [1, 5, 13, 15] :: cert04_L_266
private def cert04_L_264 : List Cell := [1, 5, 18, 19] :: cert04_L_265
private def cert04_L_263 : List Cell := [1, 5, 19] :: cert04_L_264
private def cert04_L_262 : List Cell := [1, 5, 18] :: cert04_L_263
private def cert04_L_261 : List Cell := [1, 5, 15] :: cert04_L_262
private def cert04_L_260 : List Cell := [1, 5, 13] :: cert04_L_261
private def cert04_L_259 : List Cell := [1, 5, 7] :: cert04_L_260
private def cert04_L_258 : List Cell := [1, 7, 18] :: cert04_L_259
private def cert04_L_257 : List Cell := [1, 7, 15] :: cert04_L_258
private def cert04_L_256 : List Cell := [1, 9, 11, 19] :: cert04_L_257
private def cert04_L_255 : List Cell := [1, 9, 11, 15] :: cert04_L_256
private def cert04_L_254 : List Cell := [1, 9, 13, 19] :: cert04_L_255
private def cert04_L_253 : List Cell := [1, 9, 13, 15] :: cert04_L_254
private def cert04_L_252 : List Cell := [1, 9, 19] :: cert04_L_253
private def cert04_L_251 : List Cell := [1, 9, 15] :: cert04_L_252
private def cert04_L_250 : List Cell := [1, 9, 13] :: cert04_L_251
private def cert04_L_249 : List Cell := [1, 9, 11] :: cert04_L_250
private def cert04_L_248 : List Cell := [1, 11, 19] :: cert04_L_249
private def cert04_L_247 : List Cell := [1, 11, 15] :: cert04_L_248
private def cert04_L_246 : List Cell := [1, 13, 19] :: cert04_L_247
private def cert04_L_245 : List Cell := [1, 13, 15] :: cert04_L_246
private def cert04_L_244 : List Cell := [1, 16, 17, 19] :: cert04_L_245
private def cert04_L_243 : List Cell := [1, 16, 17, 18] :: cert04_L_244
private def cert04_L_242 : List Cell := [1, 16, 18, 19] :: cert04_L_243
private def cert04_L_241 : List Cell := [1, 16, 19] :: cert04_L_242
private def cert04_L_240 : List Cell := [1, 16, 18] :: cert04_L_241
private def cert04_L_239 : List Cell := [1, 16, 17] :: cert04_L_240
private def cert04_L_238 : List Cell := [1, 17, 19] :: cert04_L_239
private def cert04_L_237 : List Cell := [1, 17, 18] :: cert04_L_238
private def cert04_L_236 : List Cell := [1, 18, 19] :: cert04_L_237
private def cert04_L_235 : List Cell := [1, 19] :: cert04_L_236
private def cert04_L_234 : List Cell := [1, 18] :: cert04_L_235
private def cert04_L_233 : List Cell := [1, 17] :: cert04_L_234
private def cert04_L_232 : List Cell := [1, 16] :: cert04_L_233
private def cert04_L_231 : List Cell := [1, 15] :: cert04_L_232
private def cert04_L_230 : List Cell := [1, 13] :: cert04_L_231
private def cert04_L_229 : List Cell := [1, 11] :: cert04_L_230
private def cert04_L_228 : List Cell := [1, 9] :: cert04_L_229
private def cert04_L_227 : List Cell := [1, 7] :: cert04_L_228
private def cert04_L_226 : List Cell := [1, 5] :: cert04_L_227
private def cert04_L_225 : List Cell := [1, 3] :: cert04_L_226
private def cert04_L_224 : List Cell := [2, 3, 7, 18] :: cert04_L_225
private def cert04_L_223 : List Cell := [2, 3, 7, 15] :: cert04_L_224
private def cert04_L_222 : List Cell := [2, 3, 11, 19] :: cert04_L_223
private def cert04_L_221 : List Cell := [2, 3, 11, 15] :: cert04_L_222
private def cert04_L_220 : List Cell := [2, 3, 17, 19] :: cert04_L_221
private def cert04_L_219 : List Cell := [2, 3, 17, 18] :: cert04_L_220
private def cert04_L_218 : List Cell := [2, 3, 19] :: cert04_L_219
private def cert04_L_217 : List Cell := [2, 3, 18] :: cert04_L_218
private def cert04_L_216 : List Cell := [2, 3, 17] :: cert04_L_217
private def cert04_L_215 : List Cell := [2, 3, 15] :: cert04_L_216
private def cert04_L_214 : List Cell := [2, 3, 11] :: cert04_L_215
private def cert04_L_213 : List Cell := [2, 3, 7] :: cert04_L_214
private def cert04_L_212 : List Cell := [2, 6, 7, 18] :: cert04_L_213
private def cert04_L_211 : List Cell := [2, 6, 7, 15] :: cert04_L_212
private def cert04_L_210 : List Cell := [2, 6, 14, 19] :: cert04_L_211
private def cert04_L_209 : List Cell := [2, 6, 14, 15] :: cert04_L_210
private def cert04_L_208 : List Cell := [2, 6, 18, 19] :: cert04_L_209
private def cert04_L_207 : List Cell := [2, 6, 19] :: cert04_L_208
private def cert04_L_206 : List Cell := [2, 6, 18] :: cert04_L_207
private def cert04_L_205 : List Cell := [2, 6, 15] :: cert04_L_206
private def cert04_L_204 : List Cell := [2, 6, 14] :: cert04_L_205
private def cert04_L_203 : List Cell := [2, 6, 7] :: cert04_L_204
private def cert04_L_202 : List Cell := [2, 7, 18] :: cert04_L_203
private def cert04_L_201 : List Cell := [2, 7, 15] :: cert04_L_202
private def cert04_L_200 : List Cell := [2, 10, 11, 19] :: cert04_L_201
private def cert04_L_199 : List Cell := [2, 10, 11, 15] :: cert04_L_200
private def cert04_L_198 : List Cell := [2, 10, 14, 19] :: cert04_L_199
private def cert04_L_197 : List Cell := [2, 10, 14, 15] :: cert04_L_198
private def cert04_L_196 : List Cell := [2, 10, 19] :: cert04_L_197
private def cert04_L_195 : List Cell := [2, 10, 15] :: cert04_L_196
private def cert04_L_194 : List Cell := [2, 10, 14] :: cert04_L_195
private def cert04_L_193 : List Cell := [2, 10, 11] :: cert04_L_194
private def cert04_L_192 : List Cell := [2, 11, 19] :: cert04_L_193
private def cert04_L_191 : List Cell := [2, 11, 15] :: cert04_L_192
private def cert04_L_190 : List Cell := [2, 14, 19] :: cert04_L_191
private def cert04_L_189 : List Cell := [2, 14, 15] :: cert04_L_190
private def cert04_L_188 : List Cell := [2, 17, 18, 19] :: cert04_L_189
private def cert04_L_187 : List Cell := [2, 17, 19] :: cert04_L_188
private def cert04_L_186 : List Cell := [2, 17, 18] :: cert04_L_187
private def cert04_L_185 : List Cell := [2, 18, 19] :: cert04_L_186
private def cert04_L_184 : List Cell := [2, 19] :: cert04_L_185
private def cert04_L_183 : List Cell := [2, 18] :: cert04_L_184
private def cert04_L_182 : List Cell := [2, 17] :: cert04_L_183
private def cert04_L_181 : List Cell := [2, 15] :: cert04_L_182
private def cert04_L_180 : List Cell := [2, 14] :: cert04_L_181
private def cert04_L_179 : List Cell := [2, 11] :: cert04_L_180
private def cert04_L_178 : List Cell := [2, 10] :: cert04_L_179
private def cert04_L_177 : List Cell := [2, 7] :: cert04_L_178
private def cert04_L_176 : List Cell := [2, 6] :: cert04_L_177
private def cert04_L_175 : List Cell := [2, 3] :: cert04_L_176
private def cert04_L_174 : List Cell := [3, 7, 18] :: cert04_L_175
private def cert04_L_173 : List Cell := [3, 7, 15] :: cert04_L_174
private def cert04_L_172 : List Cell := [3, 11, 19] :: cert04_L_173
private def cert04_L_171 : List Cell := [3, 11, 15] :: cert04_L_172
private def cert04_L_170 : List Cell := [3, 17, 19] :: cert04_L_171
private def cert04_L_169 : List Cell := [3, 17, 18] :: cert04_L_170
private def cert04_L_168 : List Cell := [3, 19] :: cert04_L_169
private def cert04_L_167 : List Cell := [3, 18] :: cert04_L_168
private def cert04_L_166 : List Cell := [3, 17] :: cert04_L_167
private def cert04_L_165 : List Cell := [3, 15] :: cert04_L_166
private def cert04_L_164 : List Cell := [3, 11] :: cert04_L_165
private def cert04_L_163 : List Cell := [3, 7] :: cert04_L_164
private def cert04_L_162 : List Cell := [4, 5, 7, 18] :: cert04_L_163
private def cert04_L_161 : List Cell := [4, 5, 7, 15] :: cert04_L_162
private def cert04_L_160 : List Cell := [4, 5, 13, 19] :: cert04_L_161
private def cert04_L_159 : List Cell := [4, 5, 13, 15] :: cert04_L_160
private def cert04_L_158 : List Cell := [4, 5, 18, 19] :: cert04_L_159
private def cert04_L_157 : List Cell := [4, 5, 19] :: cert04_L_158
private def cert04_L_156 : List Cell := [4, 5, 18] :: cert04_L_157
private def cert04_L_155 : List Cell := [4, 5, 15] :: cert04_L_156
private def cert04_L_154 : List Cell := [4, 5, 13] :: cert04_L_155
private def cert04_L_153 : List Cell := [4, 5, 7] :: cert04_L_154
private def cert04_L_152 : List Cell := [4, 6, 7, 18] :: cert04_L_153
private def cert04_L_151 : List Cell := [4, 6, 7, 15] :: cert04_L_152
private def cert04_L_150 : List Cell := [4, 6, 14, 19] :: cert04_L_151
private def cert04_L_149 : List Cell := [4, 6, 14, 15] :: cert04_L_150
private def cert04_L_148 : List Cell := [4, 6, 18, 19] :: cert04_L_149
private def cert04_L_147 : List Cell := [4, 6, 19] :: cert04_L_148
private def cert04_L_146 : List Cell := [4, 6, 18] :: cert04_L_147
private def cert04_L_145 : List Cell := [4, 6, 15] :: cert04_L_146
private def cert04_L_144 : List Cell := [4, 6, 14] :: cert04_L_145
private def cert04_L_143 : List Cell := [4, 6, 7] :: cert04_L_144
private def cert04_L_142 : List Cell := [4, 7, 18] :: cert04_L_143
private def cert04_L_141 : List Cell := [4, 7, 15] :: cert04_L_142
private def cert04_L_140 : List Cell := [4, 12, 13, 19] :: cert04_L_141
private def cert04_L_139 : List Cell := [4, 12, 13, 15] :: cert04_L_140
private def cert04_L_138 : List Cell := [4, 12, 14, 19] :: cert04_L_139
private def cert04_L_137 : List Cell := [4, 12, 14, 15] :: cert04_L_138
private def cert04_L_136 : List Cell := [4, 12, 19] :: cert04_L_137
private def cert04_L_135 : List Cell := [4, 12, 15] :: cert04_L_136
private def cert04_L_134 : List Cell := [4, 12, 14] :: cert04_L_135
private def cert04_L_133 : List Cell := [4, 12, 13] :: cert04_L_134
private def cert04_L_132 : List Cell := [4, 13, 19] :: cert04_L_133
private def cert04_L_131 : List Cell := [4, 13, 15] :: cert04_L_132
private def cert04_L_130 : List Cell := [4, 14, 19] :: cert04_L_131
private def cert04_L_129 : List Cell := [4, 14, 15] :: cert04_L_130
private def cert04_L_128 : List Cell := [4, 18, 19] :: cert04_L_129
private def cert04_L_127 : List Cell := [4, 19] :: cert04_L_128
private def cert04_L_126 : List Cell := [4, 18] :: cert04_L_127
private def cert04_L_125 : List Cell := [4, 15] :: cert04_L_126
private def cert04_L_124 : List Cell := [4, 14] :: cert04_L_125
private def cert04_L_123 : List Cell := [4, 13] :: cert04_L_124
private def cert04_L_122 : List Cell := [4, 12] :: cert04_L_123
private def cert04_L_121 : List Cell := [4, 7] :: cert04_L_122
private def cert04_L_120 : List Cell := [4, 6] :: cert04_L_121
private def cert04_L_119 : List Cell := [4, 5] :: cert04_L_120
private def cert04_L_118 : List Cell := [5, 7, 18] :: cert04_L_119
private def cert04_L_117 : List Cell := [5, 7, 15] :: cert04_L_118
private def cert04_L_116 : List Cell := [5, 13, 19] :: cert04_L_117
private def cert04_L_115 : List Cell := [5, 13, 15] :: cert04_L_116
private def cert04_L_114 : List Cell := [5, 18, 19] :: cert04_L_115
private def cert04_L_113 : List Cell := [5, 19] :: cert04_L_114
private def cert04_L_112 : List Cell := [5, 18] :: cert04_L_113
private def cert04_L_111 : List Cell := [5, 15] :: cert04_L_112
private def cert04_L_110 : List Cell := [5, 13] :: cert04_L_111
private def cert04_L_109 : List Cell := [5, 7] :: cert04_L_110
private def cert04_L_108 : List Cell := [6, 7, 18] :: cert04_L_109
private def cert04_L_107 : List Cell := [6, 7, 15] :: cert04_L_108
private def cert04_L_106 : List Cell := [6, 14, 19] :: cert04_L_107
private def cert04_L_105 : List Cell := [6, 14, 15] :: cert04_L_106
private def cert04_L_104 : List Cell := [6, 18, 19] :: cert04_L_105
private def cert04_L_103 : List Cell := [6, 19] :: cert04_L_104
private def cert04_L_102 : List Cell := [6, 18] :: cert04_L_103
private def cert04_L_101 : List Cell := [6, 15] :: cert04_L_102
private def cert04_L_100 : List Cell := [6, 14] :: cert04_L_101
private def cert04_L_99 : List Cell := [6, 7] :: cert04_L_100
private def cert04_L_98 : List Cell := [7, 18] :: cert04_L_99
private def cert04_L_97 : List Cell := [7, 15] :: cert04_L_98
private def cert04_L_96 : List Cell := [8, 9, 11, 19] :: cert04_L_97
private def cert04_L_95 : List Cell := [8, 9, 11, 15] :: cert04_L_96
private def cert04_L_94 : List Cell := [8, 9, 13, 19] :: cert04_L_95
private def cert04_L_93 : List Cell := [8, 9, 13, 15] :: cert04_L_94
private def cert04_L_92 : List Cell := [8, 9, 19] :: cert04_L_93
private def cert04_L_91 : List Cell := [8, 9, 15] :: cert04_L_92
private def cert04_L_90 : List Cell := [8, 9, 13] :: cert04_L_91
private def cert04_L_89 : List Cell := [8, 9, 11] :: cert04_L_90
private def cert04_L_88 : List Cell := [8, 10, 11, 19] :: cert04_L_89
private def cert04_L_87 : List Cell := [8, 10, 11, 15] :: cert04_L_88
private def cert04_L_86 : List Cell := [8, 10, 14, 19] :: cert04_L_87
private def cert04_L_85 : List Cell := [8, 10, 14, 15] :: cert04_L_86
private def cert04_L_84 : List Cell := [8, 10, 19] :: cert04_L_85
private def cert04_L_83 : List Cell := [8, 10, 15] :: cert04_L_84
private def cert04_L_82 : List Cell := [8, 10, 14] :: cert04_L_83
private def cert04_L_81 : List Cell := [8, 10, 11] :: cert04_L_82
private def cert04_L_80 : List Cell := [8, 11, 19] :: cert04_L_81
private def cert04_L_79 : List Cell := [8, 11, 15] :: cert04_L_80
private def cert04_L_78 : List Cell := [8, 12, 13, 19] :: cert04_L_79
private def cert04_L_77 : List Cell := [8, 12, 13, 15] :: cert04_L_78
private def cert04_L_76 : List Cell := [8, 12, 14, 19] :: cert04_L_77
private def cert04_L_75 : List Cell := [8, 12, 14, 15] :: cert04_L_76
private def cert04_L_74 : List Cell := [8, 12, 19] :: cert04_L_75
private def cert04_L_73 : List Cell := [8, 12, 15] :: cert04_L_74
private def cert04_L_72 : List Cell := [8, 12, 14] :: cert04_L_73
private def cert04_L_71 : List Cell := [8, 12, 13] :: cert04_L_72
private def cert04_L_70 : List Cell := [8, 13, 19] :: cert04_L_71
private def cert04_L_69 : List Cell := [8, 13, 15] :: cert04_L_70
private def cert04_L_68 : List Cell := [8, 14, 19] :: cert04_L_69
private def cert04_L_67 : List Cell := [8, 14, 15] :: cert04_L_68
private def cert04_L_66 : List Cell := [8, 19] :: cert04_L_67
private def cert04_L_65 : List Cell := [8, 15] :: cert04_L_66
private def cert04_L_64 : List Cell := [8, 14] :: cert04_L_65
private def cert04_L_63 : List Cell := [8, 13] :: cert04_L_64
private def cert04_L_62 : List Cell := [8, 12] :: cert04_L_63
private def cert04_L_61 : List Cell := [8, 11] :: cert04_L_62
private def cert04_L_60 : List Cell := [8, 10] :: cert04_L_61
private def cert04_L_59 : List Cell := [8, 9] :: cert04_L_60
private def cert04_L_58 : List Cell := [9, 11, 19] :: cert04_L_59
private def cert04_L_57 : List Cell := [9, 11, 15] :: cert04_L_58
private def cert04_L_56 : List Cell := [9, 13, 19] :: cert04_L_57
private def cert04_L_55 : List Cell := [9, 13, 15] :: cert04_L_56
private def cert04_L_54 : List Cell := [9, 19] :: cert04_L_55
private def cert04_L_53 : List Cell := [9, 15] :: cert04_L_54
private def cert04_L_52 : List Cell := [9, 13] :: cert04_L_53
private def cert04_L_51 : List Cell := [9, 11] :: cert04_L_52
private def cert04_L_50 : List Cell := [10, 11, 19] :: cert04_L_51
private def cert04_L_49 : List Cell := [10, 11, 15] :: cert04_L_50
private def cert04_L_48 : List Cell := [10, 14, 19] :: cert04_L_49
private def cert04_L_47 : List Cell := [10, 14, 15] :: cert04_L_48
private def cert04_L_46 : List Cell := [10, 19] :: cert04_L_47
private def cert04_L_45 : List Cell := [10, 15] :: cert04_L_46
private def cert04_L_44 : List Cell := [10, 14] :: cert04_L_45
private def cert04_L_43 : List Cell := [10, 11] :: cert04_L_44
private def cert04_L_42 : List Cell := [11, 19] :: cert04_L_43
private def cert04_L_41 : List Cell := [11, 15] :: cert04_L_42
private def cert04_L_40 : List Cell := [12, 13, 19] :: cert04_L_41
private def cert04_L_39 : List Cell := [12, 13, 15] :: cert04_L_40
private def cert04_L_38 : List Cell := [12, 14, 19] :: cert04_L_39
private def cert04_L_37 : List Cell := [12, 14, 15] :: cert04_L_38
private def cert04_L_36 : List Cell := [12, 19] :: cert04_L_37
private def cert04_L_35 : List Cell := [12, 15] :: cert04_L_36
private def cert04_L_34 : List Cell := [12, 14] :: cert04_L_35
private def cert04_L_33 : List Cell := [12, 13] :: cert04_L_34
private def cert04_L_32 : List Cell := [13, 19] :: cert04_L_33
private def cert04_L_31 : List Cell := [13, 15] :: cert04_L_32
private def cert04_L_30 : List Cell := [14, 19] :: cert04_L_31
private def cert04_L_29 : List Cell := [14, 15] :: cert04_L_30
private def cert04_L_28 : List Cell := [16, 17, 19] :: cert04_L_29
private def cert04_L_27 : List Cell := [16, 17, 18] :: cert04_L_28
private def cert04_L_26 : List Cell := [16, 18, 19] :: cert04_L_27
private def cert04_L_25 : List Cell := [16, 19] :: cert04_L_26
private def cert04_L_24 : List Cell := [16, 18] :: cert04_L_25
private def cert04_L_23 : List Cell := [16, 17] :: cert04_L_24
private def cert04_L_22 : List Cell := [17, 18, 19] :: cert04_L_23
private def cert04_L_21 : List Cell := [17, 19] :: cert04_L_22
private def cert04_L_20 : List Cell := [17, 18] :: cert04_L_21
private def cert04_L_19 : List Cell := [18, 19] :: cert04_L_20
private def cert04_L_18 : List Cell := [19] :: cert04_L_19
private def cert04_L_17 : List Cell := [18] :: cert04_L_18
private def cert04_L_16 : List Cell := [17] :: cert04_L_17
private def cert04_L_15 : List Cell := [16] :: cert04_L_16
private def cert04_L_14 : List Cell := [15] :: cert04_L_15
private def cert04_L_13 : List Cell := [14] :: cert04_L_14
private def cert04_L_12 : List Cell := [13] :: cert04_L_13
private def cert04_L_11 : List Cell := [12] :: cert04_L_12
private def cert04_L_10 : List Cell := [11] :: cert04_L_11
private def cert04_L_9 : List Cell := [10] :: cert04_L_10
private def cert04_L_8 : List Cell := [9] :: cert04_L_9
private def cert04_L_7 : List Cell := [8] :: cert04_L_8
private def cert04_L_6 : List Cell := [7] :: cert04_L_7
private def cert04_L_5 : List Cell := [6] :: cert04_L_6
private def cert04_L_4 : List Cell := [5] :: cert04_L_5
private def cert04_L_3 : List Cell := [4] :: cert04_L_4
private def cert04_L_2 : List Cell := [3] :: cert04_L_3
private def cert04_L_1 : List Cell := [2] :: cert04_L_2
private def cert04_L_0 : List Cell := [1] :: cert04_L_1
private theorem cert04_U_eq : «universe» 3 = cert04_U_0 := by decide +kernel
private theorem cert04_I_eq : initial 3 = cert04_I_0 := by decide +kernel
private theorem cert04_L_eq : live 3 pairs3 = cert04_L_0 := by decide +kernel
private theorem cert04_distinct_391 : distinct cert04_U_391 = true := rfl
private theorem cert04_fresh_390 : !cert04_U_391.contains [1, 3, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_390 : distinct cert04_U_390 = true :=
  cert04_distinct_cons [1, 3, 7, 15, 19] cert04_U_391 cert04_fresh_390 cert04_distinct_391
private theorem cert04_fresh_389 : !cert04_U_390.contains [1, 3, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_389 : distinct cert04_U_389 = true :=
  cert04_distinct_cons [1, 3, 7, 18, 19] cert04_U_390 cert04_fresh_389 cert04_distinct_390
private theorem cert04_fresh_388 : !cert04_U_389.contains [1, 3, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_388 : distinct cert04_U_388 = true :=
  cert04_distinct_cons [1, 3, 7, 19] cert04_U_389 cert04_fresh_388 cert04_distinct_389
private theorem cert04_fresh_387 : !cert04_U_388.contains [1, 3, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_387 : distinct cert04_U_387 = true :=
  cert04_distinct_cons [1, 3, 7, 18] cert04_U_388 cert04_fresh_387 cert04_distinct_388
private theorem cert04_fresh_386 : !cert04_U_387.contains [1, 3, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_386 : distinct cert04_U_386 = true :=
  cert04_distinct_cons [1, 3, 7, 15] cert04_U_387 cert04_fresh_386 cert04_distinct_387
private theorem cert04_fresh_385 : !cert04_U_386.contains [1, 3, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_385 : distinct cert04_U_385 = true :=
  cert04_distinct_cons [1, 3, 11, 15, 19] cert04_U_386 cert04_fresh_385 cert04_distinct_386
private theorem cert04_fresh_384 : !cert04_U_385.contains [1, 3, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_384 : distinct cert04_U_384 = true :=
  cert04_distinct_cons [1, 3, 11, 19] cert04_U_385 cert04_fresh_384 cert04_distinct_385
private theorem cert04_fresh_383 : !cert04_U_384.contains [1, 3, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_383 : distinct cert04_U_383 = true :=
  cert04_distinct_cons [1, 3, 11, 15] cert04_U_384 cert04_fresh_383 cert04_distinct_384
private theorem cert04_fresh_382 : !cert04_U_383.contains [1, 3, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_382 : distinct cert04_U_382 = true :=
  cert04_distinct_cons [1, 3, 15, 19] cert04_U_383 cert04_fresh_382 cert04_distinct_383
private theorem cert04_fresh_381 : !cert04_U_382.contains [1, 3, 17, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_381 : distinct cert04_U_381 = true :=
  cert04_distinct_cons [1, 3, 17, 18, 19] cert04_U_382 cert04_fresh_381 cert04_distinct_382
private theorem cert04_fresh_380 : !cert04_U_381.contains [1, 3, 17, 19] = true := by decide +kernel
private theorem cert04_distinct_380 : distinct cert04_U_380 = true :=
  cert04_distinct_cons [1, 3, 17, 19] cert04_U_381 cert04_fresh_380 cert04_distinct_381
private theorem cert04_fresh_379 : !cert04_U_380.contains [1, 3, 17, 18] = true := by decide +kernel
private theorem cert04_distinct_379 : distinct cert04_U_379 = true :=
  cert04_distinct_cons [1, 3, 17, 18] cert04_U_380 cert04_fresh_379 cert04_distinct_380
private theorem cert04_fresh_378 : !cert04_U_379.contains [1, 3, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_378 : distinct cert04_U_378 = true :=
  cert04_distinct_cons [1, 3, 18, 19] cert04_U_379 cert04_fresh_378 cert04_distinct_379
private theorem cert04_fresh_377 : !cert04_U_378.contains [1, 3, 19] = true := by decide +kernel
private theorem cert04_distinct_377 : distinct cert04_U_377 = true :=
  cert04_distinct_cons [1, 3, 19] cert04_U_378 cert04_fresh_377 cert04_distinct_378
private theorem cert04_fresh_376 : !cert04_U_377.contains [1, 3, 18] = true := by decide +kernel
private theorem cert04_distinct_376 : distinct cert04_U_376 = true :=
  cert04_distinct_cons [1, 3, 18] cert04_U_377 cert04_fresh_376 cert04_distinct_377
private theorem cert04_fresh_375 : !cert04_U_376.contains [1, 3, 17] = true := by decide +kernel
private theorem cert04_distinct_375 : distinct cert04_U_375 = true :=
  cert04_distinct_cons [1, 3, 17] cert04_U_376 cert04_fresh_375 cert04_distinct_376
private theorem cert04_fresh_374 : !cert04_U_375.contains [1, 3, 15] = true := by decide +kernel
private theorem cert04_distinct_374 : distinct cert04_U_374 = true :=
  cert04_distinct_cons [1, 3, 15] cert04_U_375 cert04_fresh_374 cert04_distinct_375
private theorem cert04_fresh_373 : !cert04_U_374.contains [1, 3, 11] = true := by decide +kernel
private theorem cert04_distinct_373 : distinct cert04_U_373 = true :=
  cert04_distinct_cons [1, 3, 11] cert04_U_374 cert04_fresh_373 cert04_distinct_374
private theorem cert04_fresh_372 : !cert04_U_373.contains [1, 3, 7] = true := by decide +kernel
private theorem cert04_distinct_372 : distinct cert04_U_372 = true :=
  cert04_distinct_cons [1, 3, 7] cert04_U_373 cert04_fresh_372 cert04_distinct_373
private theorem cert04_fresh_371 : !cert04_U_372.contains [1, 5, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_371 : distinct cert04_U_371 = true :=
  cert04_distinct_cons [1, 5, 7, 15, 19] cert04_U_372 cert04_fresh_371 cert04_distinct_372
private theorem cert04_fresh_370 : !cert04_U_371.contains [1, 5, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_370 : distinct cert04_U_370 = true :=
  cert04_distinct_cons [1, 5, 7, 18, 19] cert04_U_371 cert04_fresh_370 cert04_distinct_371
private theorem cert04_fresh_369 : !cert04_U_370.contains [1, 5, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_369 : distinct cert04_U_369 = true :=
  cert04_distinct_cons [1, 5, 7, 19] cert04_U_370 cert04_fresh_369 cert04_distinct_370
private theorem cert04_fresh_368 : !cert04_U_369.contains [1, 5, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_368 : distinct cert04_U_368 = true :=
  cert04_distinct_cons [1, 5, 7, 18] cert04_U_369 cert04_fresh_368 cert04_distinct_369
private theorem cert04_fresh_367 : !cert04_U_368.contains [1, 5, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_367 : distinct cert04_U_367 = true :=
  cert04_distinct_cons [1, 5, 7, 15] cert04_U_368 cert04_fresh_367 cert04_distinct_368
private theorem cert04_fresh_366 : !cert04_U_367.contains [1, 5, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_366 : distinct cert04_U_366 = true :=
  cert04_distinct_cons [1, 5, 13, 15, 19] cert04_U_367 cert04_fresh_366 cert04_distinct_367
private theorem cert04_fresh_365 : !cert04_U_366.contains [1, 5, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_365 : distinct cert04_U_365 = true :=
  cert04_distinct_cons [1, 5, 13, 19] cert04_U_366 cert04_fresh_365 cert04_distinct_366
private theorem cert04_fresh_364 : !cert04_U_365.contains [1, 5, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_364 : distinct cert04_U_364 = true :=
  cert04_distinct_cons [1, 5, 13, 15] cert04_U_365 cert04_fresh_364 cert04_distinct_365
private theorem cert04_fresh_363 : !cert04_U_364.contains [1, 5, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_363 : distinct cert04_U_363 = true :=
  cert04_distinct_cons [1, 5, 15, 19] cert04_U_364 cert04_fresh_363 cert04_distinct_364
private theorem cert04_fresh_362 : !cert04_U_363.contains [1, 5, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_362 : distinct cert04_U_362 = true :=
  cert04_distinct_cons [1, 5, 18, 19] cert04_U_363 cert04_fresh_362 cert04_distinct_363
private theorem cert04_fresh_361 : !cert04_U_362.contains [1, 5, 19] = true := by decide +kernel
private theorem cert04_distinct_361 : distinct cert04_U_361 = true :=
  cert04_distinct_cons [1, 5, 19] cert04_U_362 cert04_fresh_361 cert04_distinct_362
private theorem cert04_fresh_360 : !cert04_U_361.contains [1, 5, 18] = true := by decide +kernel
private theorem cert04_distinct_360 : distinct cert04_U_360 = true :=
  cert04_distinct_cons [1, 5, 18] cert04_U_361 cert04_fresh_360 cert04_distinct_361
private theorem cert04_fresh_359 : !cert04_U_360.contains [1, 5, 15] = true := by decide +kernel
private theorem cert04_distinct_359 : distinct cert04_U_359 = true :=
  cert04_distinct_cons [1, 5, 15] cert04_U_360 cert04_fresh_359 cert04_distinct_360
private theorem cert04_fresh_358 : !cert04_U_359.contains [1, 5, 13] = true := by decide +kernel
private theorem cert04_distinct_358 : distinct cert04_U_358 = true :=
  cert04_distinct_cons [1, 5, 13] cert04_U_359 cert04_fresh_358 cert04_distinct_359
private theorem cert04_fresh_357 : !cert04_U_358.contains [1, 5, 7] = true := by decide +kernel
private theorem cert04_distinct_357 : distinct cert04_U_357 = true :=
  cert04_distinct_cons [1, 5, 7] cert04_U_358 cert04_fresh_357 cert04_distinct_358
private theorem cert04_fresh_356 : !cert04_U_357.contains [1, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_356 : distinct cert04_U_356 = true :=
  cert04_distinct_cons [1, 7, 15, 19] cert04_U_357 cert04_fresh_356 cert04_distinct_357
private theorem cert04_fresh_355 : !cert04_U_356.contains [1, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_355 : distinct cert04_U_355 = true :=
  cert04_distinct_cons [1, 7, 18, 19] cert04_U_356 cert04_fresh_355 cert04_distinct_356
private theorem cert04_fresh_354 : !cert04_U_355.contains [1, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_354 : distinct cert04_U_354 = true :=
  cert04_distinct_cons [1, 7, 19] cert04_U_355 cert04_fresh_354 cert04_distinct_355
private theorem cert04_fresh_353 : !cert04_U_354.contains [1, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_353 : distinct cert04_U_353 = true :=
  cert04_distinct_cons [1, 7, 18] cert04_U_354 cert04_fresh_353 cert04_distinct_354
private theorem cert04_fresh_352 : !cert04_U_353.contains [1, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_352 : distinct cert04_U_352 = true :=
  cert04_distinct_cons [1, 7, 15] cert04_U_353 cert04_fresh_352 cert04_distinct_353
private theorem cert04_fresh_351 : !cert04_U_352.contains [1, 9, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_351 : distinct cert04_U_351 = true :=
  cert04_distinct_cons [1, 9, 11, 15, 19] cert04_U_352 cert04_fresh_351 cert04_distinct_352
private theorem cert04_fresh_350 : !cert04_U_351.contains [1, 9, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_350 : distinct cert04_U_350 = true :=
  cert04_distinct_cons [1, 9, 11, 19] cert04_U_351 cert04_fresh_350 cert04_distinct_351
private theorem cert04_fresh_349 : !cert04_U_350.contains [1, 9, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_349 : distinct cert04_U_349 = true :=
  cert04_distinct_cons [1, 9, 11, 15] cert04_U_350 cert04_fresh_349 cert04_distinct_350
private theorem cert04_fresh_348 : !cert04_U_349.contains [1, 9, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_348 : distinct cert04_U_348 = true :=
  cert04_distinct_cons [1, 9, 13, 15, 19] cert04_U_349 cert04_fresh_348 cert04_distinct_349
private theorem cert04_fresh_347 : !cert04_U_348.contains [1, 9, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_347 : distinct cert04_U_347 = true :=
  cert04_distinct_cons [1, 9, 13, 19] cert04_U_348 cert04_fresh_347 cert04_distinct_348
private theorem cert04_fresh_346 : !cert04_U_347.contains [1, 9, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_346 : distinct cert04_U_346 = true :=
  cert04_distinct_cons [1, 9, 13, 15] cert04_U_347 cert04_fresh_346 cert04_distinct_347
private theorem cert04_fresh_345 : !cert04_U_346.contains [1, 9, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_345 : distinct cert04_U_345 = true :=
  cert04_distinct_cons [1, 9, 15, 19] cert04_U_346 cert04_fresh_345 cert04_distinct_346
private theorem cert04_fresh_344 : !cert04_U_345.contains [1, 9, 19] = true := by decide +kernel
private theorem cert04_distinct_344 : distinct cert04_U_344 = true :=
  cert04_distinct_cons [1, 9, 19] cert04_U_345 cert04_fresh_344 cert04_distinct_345
private theorem cert04_fresh_343 : !cert04_U_344.contains [1, 9, 15] = true := by decide +kernel
private theorem cert04_distinct_343 : distinct cert04_U_343 = true :=
  cert04_distinct_cons [1, 9, 15] cert04_U_344 cert04_fresh_343 cert04_distinct_344
private theorem cert04_fresh_342 : !cert04_U_343.contains [1, 9, 13] = true := by decide +kernel
private theorem cert04_distinct_342 : distinct cert04_U_342 = true :=
  cert04_distinct_cons [1, 9, 13] cert04_U_343 cert04_fresh_342 cert04_distinct_343
private theorem cert04_fresh_341 : !cert04_U_342.contains [1, 9, 11] = true := by decide +kernel
private theorem cert04_distinct_341 : distinct cert04_U_341 = true :=
  cert04_distinct_cons [1, 9, 11] cert04_U_342 cert04_fresh_341 cert04_distinct_342
private theorem cert04_fresh_340 : !cert04_U_341.contains [1, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_340 : distinct cert04_U_340 = true :=
  cert04_distinct_cons [1, 11, 15, 19] cert04_U_341 cert04_fresh_340 cert04_distinct_341
private theorem cert04_fresh_339 : !cert04_U_340.contains [1, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_339 : distinct cert04_U_339 = true :=
  cert04_distinct_cons [1, 11, 19] cert04_U_340 cert04_fresh_339 cert04_distinct_340
private theorem cert04_fresh_338 : !cert04_U_339.contains [1, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_338 : distinct cert04_U_338 = true :=
  cert04_distinct_cons [1, 11, 15] cert04_U_339 cert04_fresh_338 cert04_distinct_339
private theorem cert04_fresh_337 : !cert04_U_338.contains [1, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_337 : distinct cert04_U_337 = true :=
  cert04_distinct_cons [1, 13, 15, 19] cert04_U_338 cert04_fresh_337 cert04_distinct_338
private theorem cert04_fresh_336 : !cert04_U_337.contains [1, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_336 : distinct cert04_U_336 = true :=
  cert04_distinct_cons [1, 13, 19] cert04_U_337 cert04_fresh_336 cert04_distinct_337
private theorem cert04_fresh_335 : !cert04_U_336.contains [1, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_335 : distinct cert04_U_335 = true :=
  cert04_distinct_cons [1, 13, 15] cert04_U_336 cert04_fresh_335 cert04_distinct_336
private theorem cert04_fresh_334 : !cert04_U_335.contains [1, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_334 : distinct cert04_U_334 = true :=
  cert04_distinct_cons [1, 15, 19] cert04_U_335 cert04_fresh_334 cert04_distinct_335
private theorem cert04_fresh_333 : !cert04_U_334.contains [1, 16, 17, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_333 : distinct cert04_U_333 = true :=
  cert04_distinct_cons [1, 16, 17, 18, 19] cert04_U_334 cert04_fresh_333 cert04_distinct_334
private theorem cert04_fresh_332 : !cert04_U_333.contains [1, 16, 17, 19] = true := by decide +kernel
private theorem cert04_distinct_332 : distinct cert04_U_332 = true :=
  cert04_distinct_cons [1, 16, 17, 19] cert04_U_333 cert04_fresh_332 cert04_distinct_333
private theorem cert04_fresh_331 : !cert04_U_332.contains [1, 16, 17, 18] = true := by decide +kernel
private theorem cert04_distinct_331 : distinct cert04_U_331 = true :=
  cert04_distinct_cons [1, 16, 17, 18] cert04_U_332 cert04_fresh_331 cert04_distinct_332
private theorem cert04_fresh_330 : !cert04_U_331.contains [1, 16, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_330 : distinct cert04_U_330 = true :=
  cert04_distinct_cons [1, 16, 18, 19] cert04_U_331 cert04_fresh_330 cert04_distinct_331
private theorem cert04_fresh_329 : !cert04_U_330.contains [1, 16, 19] = true := by decide +kernel
private theorem cert04_distinct_329 : distinct cert04_U_329 = true :=
  cert04_distinct_cons [1, 16, 19] cert04_U_330 cert04_fresh_329 cert04_distinct_330
private theorem cert04_fresh_328 : !cert04_U_329.contains [1, 16, 18] = true := by decide +kernel
private theorem cert04_distinct_328 : distinct cert04_U_328 = true :=
  cert04_distinct_cons [1, 16, 18] cert04_U_329 cert04_fresh_328 cert04_distinct_329
private theorem cert04_fresh_327 : !cert04_U_328.contains [1, 16, 17] = true := by decide +kernel
private theorem cert04_distinct_327 : distinct cert04_U_327 = true :=
  cert04_distinct_cons [1, 16, 17] cert04_U_328 cert04_fresh_327 cert04_distinct_328
private theorem cert04_fresh_326 : !cert04_U_327.contains [1, 17, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_326 : distinct cert04_U_326 = true :=
  cert04_distinct_cons [1, 17, 18, 19] cert04_U_327 cert04_fresh_326 cert04_distinct_327
private theorem cert04_fresh_325 : !cert04_U_326.contains [1, 17, 19] = true := by decide +kernel
private theorem cert04_distinct_325 : distinct cert04_U_325 = true :=
  cert04_distinct_cons [1, 17, 19] cert04_U_326 cert04_fresh_325 cert04_distinct_326
private theorem cert04_fresh_324 : !cert04_U_325.contains [1, 17, 18] = true := by decide +kernel
private theorem cert04_distinct_324 : distinct cert04_U_324 = true :=
  cert04_distinct_cons [1, 17, 18] cert04_U_325 cert04_fresh_324 cert04_distinct_325
private theorem cert04_fresh_323 : !cert04_U_324.contains [1, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_323 : distinct cert04_U_323 = true :=
  cert04_distinct_cons [1, 18, 19] cert04_U_324 cert04_fresh_323 cert04_distinct_324
private theorem cert04_fresh_322 : !cert04_U_323.contains [1, 19] = true := by decide +kernel
private theorem cert04_distinct_322 : distinct cert04_U_322 = true :=
  cert04_distinct_cons [1, 19] cert04_U_323 cert04_fresh_322 cert04_distinct_323
private theorem cert04_fresh_321 : !cert04_U_322.contains [1, 18] = true := by decide +kernel
private theorem cert04_distinct_321 : distinct cert04_U_321 = true :=
  cert04_distinct_cons [1, 18] cert04_U_322 cert04_fresh_321 cert04_distinct_322
private theorem cert04_fresh_320 : !cert04_U_321.contains [1, 17] = true := by decide +kernel
private theorem cert04_distinct_320 : distinct cert04_U_320 = true :=
  cert04_distinct_cons [1, 17] cert04_U_321 cert04_fresh_320 cert04_distinct_321
private theorem cert04_fresh_319 : !cert04_U_320.contains [1, 16] = true := by decide +kernel
private theorem cert04_distinct_319 : distinct cert04_U_319 = true :=
  cert04_distinct_cons [1, 16] cert04_U_320 cert04_fresh_319 cert04_distinct_320
private theorem cert04_fresh_318 : !cert04_U_319.contains [1, 15] = true := by decide +kernel
private theorem cert04_distinct_318 : distinct cert04_U_318 = true :=
  cert04_distinct_cons [1, 15] cert04_U_319 cert04_fresh_318 cert04_distinct_319
private theorem cert04_fresh_317 : !cert04_U_318.contains [1, 13] = true := by decide +kernel
private theorem cert04_distinct_317 : distinct cert04_U_317 = true :=
  cert04_distinct_cons [1, 13] cert04_U_318 cert04_fresh_317 cert04_distinct_318
private theorem cert04_fresh_316 : !cert04_U_317.contains [1, 11] = true := by decide +kernel
private theorem cert04_distinct_316 : distinct cert04_U_316 = true :=
  cert04_distinct_cons [1, 11] cert04_U_317 cert04_fresh_316 cert04_distinct_317
private theorem cert04_fresh_315 : !cert04_U_316.contains [1, 9] = true := by decide +kernel
private theorem cert04_distinct_315 : distinct cert04_U_315 = true :=
  cert04_distinct_cons [1, 9] cert04_U_316 cert04_fresh_315 cert04_distinct_316
private theorem cert04_fresh_314 : !cert04_U_315.contains [1, 7] = true := by decide +kernel
private theorem cert04_distinct_314 : distinct cert04_U_314 = true :=
  cert04_distinct_cons [1, 7] cert04_U_315 cert04_fresh_314 cert04_distinct_315
private theorem cert04_fresh_313 : !cert04_U_314.contains [1, 5] = true := by decide +kernel
private theorem cert04_distinct_313 : distinct cert04_U_313 = true :=
  cert04_distinct_cons [1, 5] cert04_U_314 cert04_fresh_313 cert04_distinct_314
private theorem cert04_fresh_312 : !cert04_U_313.contains [1, 3] = true := by decide +kernel
private theorem cert04_distinct_312 : distinct cert04_U_312 = true :=
  cert04_distinct_cons [1, 3] cert04_U_313 cert04_fresh_312 cert04_distinct_313
private theorem cert04_fresh_311 : !cert04_U_312.contains [2, 3, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_311 : distinct cert04_U_311 = true :=
  cert04_distinct_cons [2, 3, 7, 15, 19] cert04_U_312 cert04_fresh_311 cert04_distinct_312
private theorem cert04_fresh_310 : !cert04_U_311.contains [2, 3, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_310 : distinct cert04_U_310 = true :=
  cert04_distinct_cons [2, 3, 7, 18, 19] cert04_U_311 cert04_fresh_310 cert04_distinct_311
private theorem cert04_fresh_309 : !cert04_U_310.contains [2, 3, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_309 : distinct cert04_U_309 = true :=
  cert04_distinct_cons [2, 3, 7, 19] cert04_U_310 cert04_fresh_309 cert04_distinct_310
private theorem cert04_fresh_308 : !cert04_U_309.contains [2, 3, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_308 : distinct cert04_U_308 = true :=
  cert04_distinct_cons [2, 3, 7, 18] cert04_U_309 cert04_fresh_308 cert04_distinct_309
private theorem cert04_fresh_307 : !cert04_U_308.contains [2, 3, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_307 : distinct cert04_U_307 = true :=
  cert04_distinct_cons [2, 3, 7, 15] cert04_U_308 cert04_fresh_307 cert04_distinct_308
private theorem cert04_fresh_306 : !cert04_U_307.contains [2, 3, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_306 : distinct cert04_U_306 = true :=
  cert04_distinct_cons [2, 3, 11, 15, 19] cert04_U_307 cert04_fresh_306 cert04_distinct_307
private theorem cert04_fresh_305 : !cert04_U_306.contains [2, 3, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_305 : distinct cert04_U_305 = true :=
  cert04_distinct_cons [2, 3, 11, 19] cert04_U_306 cert04_fresh_305 cert04_distinct_306
private theorem cert04_fresh_304 : !cert04_U_305.contains [2, 3, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_304 : distinct cert04_U_304 = true :=
  cert04_distinct_cons [2, 3, 11, 15] cert04_U_305 cert04_fresh_304 cert04_distinct_305
private theorem cert04_fresh_303 : !cert04_U_304.contains [2, 3, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_303 : distinct cert04_U_303 = true :=
  cert04_distinct_cons [2, 3, 15, 19] cert04_U_304 cert04_fresh_303 cert04_distinct_304
private theorem cert04_fresh_302 : !cert04_U_303.contains [2, 3, 17, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_302 : distinct cert04_U_302 = true :=
  cert04_distinct_cons [2, 3, 17, 18, 19] cert04_U_303 cert04_fresh_302 cert04_distinct_303
private theorem cert04_fresh_301 : !cert04_U_302.contains [2, 3, 17, 19] = true := by decide +kernel
private theorem cert04_distinct_301 : distinct cert04_U_301 = true :=
  cert04_distinct_cons [2, 3, 17, 19] cert04_U_302 cert04_fresh_301 cert04_distinct_302
private theorem cert04_fresh_300 : !cert04_U_301.contains [2, 3, 17, 18] = true := by decide +kernel
private theorem cert04_distinct_300 : distinct cert04_U_300 = true :=
  cert04_distinct_cons [2, 3, 17, 18] cert04_U_301 cert04_fresh_300 cert04_distinct_301
private theorem cert04_fresh_299 : !cert04_U_300.contains [2, 3, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_299 : distinct cert04_U_299 = true :=
  cert04_distinct_cons [2, 3, 18, 19] cert04_U_300 cert04_fresh_299 cert04_distinct_300
private theorem cert04_fresh_298 : !cert04_U_299.contains [2, 3, 19] = true := by decide +kernel
private theorem cert04_distinct_298 : distinct cert04_U_298 = true :=
  cert04_distinct_cons [2, 3, 19] cert04_U_299 cert04_fresh_298 cert04_distinct_299
private theorem cert04_fresh_297 : !cert04_U_298.contains [2, 3, 18] = true := by decide +kernel
private theorem cert04_distinct_297 : distinct cert04_U_297 = true :=
  cert04_distinct_cons [2, 3, 18] cert04_U_298 cert04_fresh_297 cert04_distinct_298
private theorem cert04_fresh_296 : !cert04_U_297.contains [2, 3, 17] = true := by decide +kernel
private theorem cert04_distinct_296 : distinct cert04_U_296 = true :=
  cert04_distinct_cons [2, 3, 17] cert04_U_297 cert04_fresh_296 cert04_distinct_297
private theorem cert04_fresh_295 : !cert04_U_296.contains [2, 3, 15] = true := by decide +kernel
private theorem cert04_distinct_295 : distinct cert04_U_295 = true :=
  cert04_distinct_cons [2, 3, 15] cert04_U_296 cert04_fresh_295 cert04_distinct_296
private theorem cert04_fresh_294 : !cert04_U_295.contains [2, 3, 11] = true := by decide +kernel
private theorem cert04_distinct_294 : distinct cert04_U_294 = true :=
  cert04_distinct_cons [2, 3, 11] cert04_U_295 cert04_fresh_294 cert04_distinct_295
private theorem cert04_fresh_293 : !cert04_U_294.contains [2, 3, 7] = true := by decide +kernel
private theorem cert04_distinct_293 : distinct cert04_U_293 = true :=
  cert04_distinct_cons [2, 3, 7] cert04_U_294 cert04_fresh_293 cert04_distinct_294
private theorem cert04_fresh_292 : !cert04_U_293.contains [2, 6, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_292 : distinct cert04_U_292 = true :=
  cert04_distinct_cons [2, 6, 7, 15, 19] cert04_U_293 cert04_fresh_292 cert04_distinct_293
private theorem cert04_fresh_291 : !cert04_U_292.contains [2, 6, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_291 : distinct cert04_U_291 = true :=
  cert04_distinct_cons [2, 6, 7, 18, 19] cert04_U_292 cert04_fresh_291 cert04_distinct_292
private theorem cert04_fresh_290 : !cert04_U_291.contains [2, 6, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_290 : distinct cert04_U_290 = true :=
  cert04_distinct_cons [2, 6, 7, 19] cert04_U_291 cert04_fresh_290 cert04_distinct_291
private theorem cert04_fresh_289 : !cert04_U_290.contains [2, 6, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_289 : distinct cert04_U_289 = true :=
  cert04_distinct_cons [2, 6, 7, 18] cert04_U_290 cert04_fresh_289 cert04_distinct_290
private theorem cert04_fresh_288 : !cert04_U_289.contains [2, 6, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_288 : distinct cert04_U_288 = true :=
  cert04_distinct_cons [2, 6, 7, 15] cert04_U_289 cert04_fresh_288 cert04_distinct_289
private theorem cert04_fresh_287 : !cert04_U_288.contains [2, 6, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_287 : distinct cert04_U_287 = true :=
  cert04_distinct_cons [2, 6, 14, 15, 19] cert04_U_288 cert04_fresh_287 cert04_distinct_288
private theorem cert04_fresh_286 : !cert04_U_287.contains [2, 6, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_286 : distinct cert04_U_286 = true :=
  cert04_distinct_cons [2, 6, 14, 19] cert04_U_287 cert04_fresh_286 cert04_distinct_287
private theorem cert04_fresh_285 : !cert04_U_286.contains [2, 6, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_285 : distinct cert04_U_285 = true :=
  cert04_distinct_cons [2, 6, 14, 15] cert04_U_286 cert04_fresh_285 cert04_distinct_286
private theorem cert04_fresh_284 : !cert04_U_285.contains [2, 6, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_284 : distinct cert04_U_284 = true :=
  cert04_distinct_cons [2, 6, 15, 19] cert04_U_285 cert04_fresh_284 cert04_distinct_285
private theorem cert04_fresh_283 : !cert04_U_284.contains [2, 6, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_283 : distinct cert04_U_283 = true :=
  cert04_distinct_cons [2, 6, 18, 19] cert04_U_284 cert04_fresh_283 cert04_distinct_284
private theorem cert04_fresh_282 : !cert04_U_283.contains [2, 6, 19] = true := by decide +kernel
private theorem cert04_distinct_282 : distinct cert04_U_282 = true :=
  cert04_distinct_cons [2, 6, 19] cert04_U_283 cert04_fresh_282 cert04_distinct_283
private theorem cert04_fresh_281 : !cert04_U_282.contains [2, 6, 18] = true := by decide +kernel
private theorem cert04_distinct_281 : distinct cert04_U_281 = true :=
  cert04_distinct_cons [2, 6, 18] cert04_U_282 cert04_fresh_281 cert04_distinct_282
private theorem cert04_fresh_280 : !cert04_U_281.contains [2, 6, 15] = true := by decide +kernel
private theorem cert04_distinct_280 : distinct cert04_U_280 = true :=
  cert04_distinct_cons [2, 6, 15] cert04_U_281 cert04_fresh_280 cert04_distinct_281
private theorem cert04_fresh_279 : !cert04_U_280.contains [2, 6, 14] = true := by decide +kernel
private theorem cert04_distinct_279 : distinct cert04_U_279 = true :=
  cert04_distinct_cons [2, 6, 14] cert04_U_280 cert04_fresh_279 cert04_distinct_280
private theorem cert04_fresh_278 : !cert04_U_279.contains [2, 6, 7] = true := by decide +kernel
private theorem cert04_distinct_278 : distinct cert04_U_278 = true :=
  cert04_distinct_cons [2, 6, 7] cert04_U_279 cert04_fresh_278 cert04_distinct_279
private theorem cert04_fresh_277 : !cert04_U_278.contains [2, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_277 : distinct cert04_U_277 = true :=
  cert04_distinct_cons [2, 7, 15, 19] cert04_U_278 cert04_fresh_277 cert04_distinct_278
private theorem cert04_fresh_276 : !cert04_U_277.contains [2, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_276 : distinct cert04_U_276 = true :=
  cert04_distinct_cons [2, 7, 18, 19] cert04_U_277 cert04_fresh_276 cert04_distinct_277
private theorem cert04_fresh_275 : !cert04_U_276.contains [2, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_275 : distinct cert04_U_275 = true :=
  cert04_distinct_cons [2, 7, 19] cert04_U_276 cert04_fresh_275 cert04_distinct_276
private theorem cert04_fresh_274 : !cert04_U_275.contains [2, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_274 : distinct cert04_U_274 = true :=
  cert04_distinct_cons [2, 7, 18] cert04_U_275 cert04_fresh_274 cert04_distinct_275
private theorem cert04_fresh_273 : !cert04_U_274.contains [2, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_273 : distinct cert04_U_273 = true :=
  cert04_distinct_cons [2, 7, 15] cert04_U_274 cert04_fresh_273 cert04_distinct_274
private theorem cert04_fresh_272 : !cert04_U_273.contains [2, 10, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_272 : distinct cert04_U_272 = true :=
  cert04_distinct_cons [2, 10, 11, 15, 19] cert04_U_273 cert04_fresh_272 cert04_distinct_273
private theorem cert04_fresh_271 : !cert04_U_272.contains [2, 10, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_271 : distinct cert04_U_271 = true :=
  cert04_distinct_cons [2, 10, 11, 19] cert04_U_272 cert04_fresh_271 cert04_distinct_272
private theorem cert04_fresh_270 : !cert04_U_271.contains [2, 10, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_270 : distinct cert04_U_270 = true :=
  cert04_distinct_cons [2, 10, 11, 15] cert04_U_271 cert04_fresh_270 cert04_distinct_271
private theorem cert04_fresh_269 : !cert04_U_270.contains [2, 10, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_269 : distinct cert04_U_269 = true :=
  cert04_distinct_cons [2, 10, 14, 15, 19] cert04_U_270 cert04_fresh_269 cert04_distinct_270
private theorem cert04_fresh_268 : !cert04_U_269.contains [2, 10, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_268 : distinct cert04_U_268 = true :=
  cert04_distinct_cons [2, 10, 14, 19] cert04_U_269 cert04_fresh_268 cert04_distinct_269
private theorem cert04_fresh_267 : !cert04_U_268.contains [2, 10, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_267 : distinct cert04_U_267 = true :=
  cert04_distinct_cons [2, 10, 14, 15] cert04_U_268 cert04_fresh_267 cert04_distinct_268
private theorem cert04_fresh_266 : !cert04_U_267.contains [2, 10, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_266 : distinct cert04_U_266 = true :=
  cert04_distinct_cons [2, 10, 15, 19] cert04_U_267 cert04_fresh_266 cert04_distinct_267
private theorem cert04_fresh_265 : !cert04_U_266.contains [2, 10, 19] = true := by decide +kernel
private theorem cert04_distinct_265 : distinct cert04_U_265 = true :=
  cert04_distinct_cons [2, 10, 19] cert04_U_266 cert04_fresh_265 cert04_distinct_266
private theorem cert04_fresh_264 : !cert04_U_265.contains [2, 10, 15] = true := by decide +kernel
private theorem cert04_distinct_264 : distinct cert04_U_264 = true :=
  cert04_distinct_cons [2, 10, 15] cert04_U_265 cert04_fresh_264 cert04_distinct_265
private theorem cert04_fresh_263 : !cert04_U_264.contains [2, 10, 14] = true := by decide +kernel
private theorem cert04_distinct_263 : distinct cert04_U_263 = true :=
  cert04_distinct_cons [2, 10, 14] cert04_U_264 cert04_fresh_263 cert04_distinct_264
private theorem cert04_fresh_262 : !cert04_U_263.contains [2, 10, 11] = true := by decide +kernel
private theorem cert04_distinct_262 : distinct cert04_U_262 = true :=
  cert04_distinct_cons [2, 10, 11] cert04_U_263 cert04_fresh_262 cert04_distinct_263
private theorem cert04_fresh_261 : !cert04_U_262.contains [2, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_261 : distinct cert04_U_261 = true :=
  cert04_distinct_cons [2, 11, 15, 19] cert04_U_262 cert04_fresh_261 cert04_distinct_262
private theorem cert04_fresh_260 : !cert04_U_261.contains [2, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_260 : distinct cert04_U_260 = true :=
  cert04_distinct_cons [2, 11, 19] cert04_U_261 cert04_fresh_260 cert04_distinct_261
private theorem cert04_fresh_259 : !cert04_U_260.contains [2, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_259 : distinct cert04_U_259 = true :=
  cert04_distinct_cons [2, 11, 15] cert04_U_260 cert04_fresh_259 cert04_distinct_260
private theorem cert04_fresh_258 : !cert04_U_259.contains [2, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_258 : distinct cert04_U_258 = true :=
  cert04_distinct_cons [2, 14, 15, 19] cert04_U_259 cert04_fresh_258 cert04_distinct_259
private theorem cert04_fresh_257 : !cert04_U_258.contains [2, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_257 : distinct cert04_U_257 = true :=
  cert04_distinct_cons [2, 14, 19] cert04_U_258 cert04_fresh_257 cert04_distinct_258
private theorem cert04_fresh_256 : !cert04_U_257.contains [2, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_256 : distinct cert04_U_256 = true :=
  cert04_distinct_cons [2, 14, 15] cert04_U_257 cert04_fresh_256 cert04_distinct_257
private theorem cert04_fresh_255 : !cert04_U_256.contains [2, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_255 : distinct cert04_U_255 = true :=
  cert04_distinct_cons [2, 15, 19] cert04_U_256 cert04_fresh_255 cert04_distinct_256
private theorem cert04_fresh_254 : !cert04_U_255.contains [2, 17, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_254 : distinct cert04_U_254 = true :=
  cert04_distinct_cons [2, 17, 18, 19] cert04_U_255 cert04_fresh_254 cert04_distinct_255
private theorem cert04_fresh_253 : !cert04_U_254.contains [2, 17, 19] = true := by decide +kernel
private theorem cert04_distinct_253 : distinct cert04_U_253 = true :=
  cert04_distinct_cons [2, 17, 19] cert04_U_254 cert04_fresh_253 cert04_distinct_254
private theorem cert04_fresh_252 : !cert04_U_253.contains [2, 17, 18] = true := by decide +kernel
private theorem cert04_distinct_252 : distinct cert04_U_252 = true :=
  cert04_distinct_cons [2, 17, 18] cert04_U_253 cert04_fresh_252 cert04_distinct_253
private theorem cert04_fresh_251 : !cert04_U_252.contains [2, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_251 : distinct cert04_U_251 = true :=
  cert04_distinct_cons [2, 18, 19] cert04_U_252 cert04_fresh_251 cert04_distinct_252
private theorem cert04_fresh_250 : !cert04_U_251.contains [2, 19] = true := by decide +kernel
private theorem cert04_distinct_250 : distinct cert04_U_250 = true :=
  cert04_distinct_cons [2, 19] cert04_U_251 cert04_fresh_250 cert04_distinct_251
private theorem cert04_fresh_249 : !cert04_U_250.contains [2, 18] = true := by decide +kernel
private theorem cert04_distinct_249 : distinct cert04_U_249 = true :=
  cert04_distinct_cons [2, 18] cert04_U_250 cert04_fresh_249 cert04_distinct_250
private theorem cert04_fresh_248 : !cert04_U_249.contains [2, 17] = true := by decide +kernel
private theorem cert04_distinct_248 : distinct cert04_U_248 = true :=
  cert04_distinct_cons [2, 17] cert04_U_249 cert04_fresh_248 cert04_distinct_249
private theorem cert04_fresh_247 : !cert04_U_248.contains [2, 15] = true := by decide +kernel
private theorem cert04_distinct_247 : distinct cert04_U_247 = true :=
  cert04_distinct_cons [2, 15] cert04_U_248 cert04_fresh_247 cert04_distinct_248
private theorem cert04_fresh_246 : !cert04_U_247.contains [2, 14] = true := by decide +kernel
private theorem cert04_distinct_246 : distinct cert04_U_246 = true :=
  cert04_distinct_cons [2, 14] cert04_U_247 cert04_fresh_246 cert04_distinct_247
private theorem cert04_fresh_245 : !cert04_U_246.contains [2, 11] = true := by decide +kernel
private theorem cert04_distinct_245 : distinct cert04_U_245 = true :=
  cert04_distinct_cons [2, 11] cert04_U_246 cert04_fresh_245 cert04_distinct_246
private theorem cert04_fresh_244 : !cert04_U_245.contains [2, 10] = true := by decide +kernel
private theorem cert04_distinct_244 : distinct cert04_U_244 = true :=
  cert04_distinct_cons [2, 10] cert04_U_245 cert04_fresh_244 cert04_distinct_245
private theorem cert04_fresh_243 : !cert04_U_244.contains [2, 7] = true := by decide +kernel
private theorem cert04_distinct_243 : distinct cert04_U_243 = true :=
  cert04_distinct_cons [2, 7] cert04_U_244 cert04_fresh_243 cert04_distinct_244
private theorem cert04_fresh_242 : !cert04_U_243.contains [2, 6] = true := by decide +kernel
private theorem cert04_distinct_242 : distinct cert04_U_242 = true :=
  cert04_distinct_cons [2, 6] cert04_U_243 cert04_fresh_242 cert04_distinct_243
private theorem cert04_fresh_241 : !cert04_U_242.contains [2, 3] = true := by decide +kernel
private theorem cert04_distinct_241 : distinct cert04_U_241 = true :=
  cert04_distinct_cons [2, 3] cert04_U_242 cert04_fresh_241 cert04_distinct_242
private theorem cert04_fresh_240 : !cert04_U_241.contains [3, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_240 : distinct cert04_U_240 = true :=
  cert04_distinct_cons [3, 7, 15, 19] cert04_U_241 cert04_fresh_240 cert04_distinct_241
private theorem cert04_fresh_239 : !cert04_U_240.contains [3, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_239 : distinct cert04_U_239 = true :=
  cert04_distinct_cons [3, 7, 18, 19] cert04_U_240 cert04_fresh_239 cert04_distinct_240
private theorem cert04_fresh_238 : !cert04_U_239.contains [3, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_238 : distinct cert04_U_238 = true :=
  cert04_distinct_cons [3, 7, 19] cert04_U_239 cert04_fresh_238 cert04_distinct_239
private theorem cert04_fresh_237 : !cert04_U_238.contains [3, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_237 : distinct cert04_U_237 = true :=
  cert04_distinct_cons [3, 7, 18] cert04_U_238 cert04_fresh_237 cert04_distinct_238
private theorem cert04_fresh_236 : !cert04_U_237.contains [3, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_236 : distinct cert04_U_236 = true :=
  cert04_distinct_cons [3, 7, 15] cert04_U_237 cert04_fresh_236 cert04_distinct_237
private theorem cert04_fresh_235 : !cert04_U_236.contains [3, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_235 : distinct cert04_U_235 = true :=
  cert04_distinct_cons [3, 11, 15, 19] cert04_U_236 cert04_fresh_235 cert04_distinct_236
private theorem cert04_fresh_234 : !cert04_U_235.contains [3, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_234 : distinct cert04_U_234 = true :=
  cert04_distinct_cons [3, 11, 19] cert04_U_235 cert04_fresh_234 cert04_distinct_235
private theorem cert04_fresh_233 : !cert04_U_234.contains [3, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_233 : distinct cert04_U_233 = true :=
  cert04_distinct_cons [3, 11, 15] cert04_U_234 cert04_fresh_233 cert04_distinct_234
private theorem cert04_fresh_232 : !cert04_U_233.contains [3, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_232 : distinct cert04_U_232 = true :=
  cert04_distinct_cons [3, 15, 19] cert04_U_233 cert04_fresh_232 cert04_distinct_233
private theorem cert04_fresh_231 : !cert04_U_232.contains [3, 17, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_231 : distinct cert04_U_231 = true :=
  cert04_distinct_cons [3, 17, 18, 19] cert04_U_232 cert04_fresh_231 cert04_distinct_232
private theorem cert04_fresh_230 : !cert04_U_231.contains [3, 17, 19] = true := by decide +kernel
private theorem cert04_distinct_230 : distinct cert04_U_230 = true :=
  cert04_distinct_cons [3, 17, 19] cert04_U_231 cert04_fresh_230 cert04_distinct_231
private theorem cert04_fresh_229 : !cert04_U_230.contains [3, 17, 18] = true := by decide +kernel
private theorem cert04_distinct_229 : distinct cert04_U_229 = true :=
  cert04_distinct_cons [3, 17, 18] cert04_U_230 cert04_fresh_229 cert04_distinct_230
private theorem cert04_fresh_228 : !cert04_U_229.contains [3, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_228 : distinct cert04_U_228 = true :=
  cert04_distinct_cons [3, 18, 19] cert04_U_229 cert04_fresh_228 cert04_distinct_229
private theorem cert04_fresh_227 : !cert04_U_228.contains [3, 19] = true := by decide +kernel
private theorem cert04_distinct_227 : distinct cert04_U_227 = true :=
  cert04_distinct_cons [3, 19] cert04_U_228 cert04_fresh_227 cert04_distinct_228
private theorem cert04_fresh_226 : !cert04_U_227.contains [3, 18] = true := by decide +kernel
private theorem cert04_distinct_226 : distinct cert04_U_226 = true :=
  cert04_distinct_cons [3, 18] cert04_U_227 cert04_fresh_226 cert04_distinct_227
private theorem cert04_fresh_225 : !cert04_U_226.contains [3, 17] = true := by decide +kernel
private theorem cert04_distinct_225 : distinct cert04_U_225 = true :=
  cert04_distinct_cons [3, 17] cert04_U_226 cert04_fresh_225 cert04_distinct_226
private theorem cert04_fresh_224 : !cert04_U_225.contains [3, 15] = true := by decide +kernel
private theorem cert04_distinct_224 : distinct cert04_U_224 = true :=
  cert04_distinct_cons [3, 15] cert04_U_225 cert04_fresh_224 cert04_distinct_225
private theorem cert04_fresh_223 : !cert04_U_224.contains [3, 11] = true := by decide +kernel
private theorem cert04_distinct_223 : distinct cert04_U_223 = true :=
  cert04_distinct_cons [3, 11] cert04_U_224 cert04_fresh_223 cert04_distinct_224
private theorem cert04_fresh_222 : !cert04_U_223.contains [3, 7] = true := by decide +kernel
private theorem cert04_distinct_222 : distinct cert04_U_222 = true :=
  cert04_distinct_cons [3, 7] cert04_U_223 cert04_fresh_222 cert04_distinct_223
private theorem cert04_fresh_221 : !cert04_U_222.contains [4, 5, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_221 : distinct cert04_U_221 = true :=
  cert04_distinct_cons [4, 5, 7, 15, 19] cert04_U_222 cert04_fresh_221 cert04_distinct_222
private theorem cert04_fresh_220 : !cert04_U_221.contains [4, 5, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_220 : distinct cert04_U_220 = true :=
  cert04_distinct_cons [4, 5, 7, 18, 19] cert04_U_221 cert04_fresh_220 cert04_distinct_221
private theorem cert04_fresh_219 : !cert04_U_220.contains [4, 5, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_219 : distinct cert04_U_219 = true :=
  cert04_distinct_cons [4, 5, 7, 19] cert04_U_220 cert04_fresh_219 cert04_distinct_220
private theorem cert04_fresh_218 : !cert04_U_219.contains [4, 5, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_218 : distinct cert04_U_218 = true :=
  cert04_distinct_cons [4, 5, 7, 18] cert04_U_219 cert04_fresh_218 cert04_distinct_219
private theorem cert04_fresh_217 : !cert04_U_218.contains [4, 5, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_217 : distinct cert04_U_217 = true :=
  cert04_distinct_cons [4, 5, 7, 15] cert04_U_218 cert04_fresh_217 cert04_distinct_218
private theorem cert04_fresh_216 : !cert04_U_217.contains [4, 5, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_216 : distinct cert04_U_216 = true :=
  cert04_distinct_cons [4, 5, 13, 15, 19] cert04_U_217 cert04_fresh_216 cert04_distinct_217
private theorem cert04_fresh_215 : !cert04_U_216.contains [4, 5, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_215 : distinct cert04_U_215 = true :=
  cert04_distinct_cons [4, 5, 13, 19] cert04_U_216 cert04_fresh_215 cert04_distinct_216
private theorem cert04_fresh_214 : !cert04_U_215.contains [4, 5, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_214 : distinct cert04_U_214 = true :=
  cert04_distinct_cons [4, 5, 13, 15] cert04_U_215 cert04_fresh_214 cert04_distinct_215
private theorem cert04_fresh_213 : !cert04_U_214.contains [4, 5, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_213 : distinct cert04_U_213 = true :=
  cert04_distinct_cons [4, 5, 15, 19] cert04_U_214 cert04_fresh_213 cert04_distinct_214
private theorem cert04_fresh_212 : !cert04_U_213.contains [4, 5, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_212 : distinct cert04_U_212 = true :=
  cert04_distinct_cons [4, 5, 18, 19] cert04_U_213 cert04_fresh_212 cert04_distinct_213
private theorem cert04_fresh_211 : !cert04_U_212.contains [4, 5, 19] = true := by decide +kernel
private theorem cert04_distinct_211 : distinct cert04_U_211 = true :=
  cert04_distinct_cons [4, 5, 19] cert04_U_212 cert04_fresh_211 cert04_distinct_212
private theorem cert04_fresh_210 : !cert04_U_211.contains [4, 5, 18] = true := by decide +kernel
private theorem cert04_distinct_210 : distinct cert04_U_210 = true :=
  cert04_distinct_cons [4, 5, 18] cert04_U_211 cert04_fresh_210 cert04_distinct_211
private theorem cert04_fresh_209 : !cert04_U_210.contains [4, 5, 15] = true := by decide +kernel
private theorem cert04_distinct_209 : distinct cert04_U_209 = true :=
  cert04_distinct_cons [4, 5, 15] cert04_U_210 cert04_fresh_209 cert04_distinct_210
private theorem cert04_fresh_208 : !cert04_U_209.contains [4, 5, 13] = true := by decide +kernel
private theorem cert04_distinct_208 : distinct cert04_U_208 = true :=
  cert04_distinct_cons [4, 5, 13] cert04_U_209 cert04_fresh_208 cert04_distinct_209
private theorem cert04_fresh_207 : !cert04_U_208.contains [4, 5, 7] = true := by decide +kernel
private theorem cert04_distinct_207 : distinct cert04_U_207 = true :=
  cert04_distinct_cons [4, 5, 7] cert04_U_208 cert04_fresh_207 cert04_distinct_208
private theorem cert04_fresh_206 : !cert04_U_207.contains [4, 6, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_206 : distinct cert04_U_206 = true :=
  cert04_distinct_cons [4, 6, 7, 15, 19] cert04_U_207 cert04_fresh_206 cert04_distinct_207
private theorem cert04_fresh_205 : !cert04_U_206.contains [4, 6, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_205 : distinct cert04_U_205 = true :=
  cert04_distinct_cons [4, 6, 7, 18, 19] cert04_U_206 cert04_fresh_205 cert04_distinct_206
private theorem cert04_fresh_204 : !cert04_U_205.contains [4, 6, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_204 : distinct cert04_U_204 = true :=
  cert04_distinct_cons [4, 6, 7, 19] cert04_U_205 cert04_fresh_204 cert04_distinct_205
private theorem cert04_fresh_203 : !cert04_U_204.contains [4, 6, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_203 : distinct cert04_U_203 = true :=
  cert04_distinct_cons [4, 6, 7, 18] cert04_U_204 cert04_fresh_203 cert04_distinct_204
private theorem cert04_fresh_202 : !cert04_U_203.contains [4, 6, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_202 : distinct cert04_U_202 = true :=
  cert04_distinct_cons [4, 6, 7, 15] cert04_U_203 cert04_fresh_202 cert04_distinct_203
private theorem cert04_fresh_201 : !cert04_U_202.contains [4, 6, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_201 : distinct cert04_U_201 = true :=
  cert04_distinct_cons [4, 6, 14, 15, 19] cert04_U_202 cert04_fresh_201 cert04_distinct_202
private theorem cert04_fresh_200 : !cert04_U_201.contains [4, 6, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_200 : distinct cert04_U_200 = true :=
  cert04_distinct_cons [4, 6, 14, 19] cert04_U_201 cert04_fresh_200 cert04_distinct_201
private theorem cert04_fresh_199 : !cert04_U_200.contains [4, 6, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_199 : distinct cert04_U_199 = true :=
  cert04_distinct_cons [4, 6, 14, 15] cert04_U_200 cert04_fresh_199 cert04_distinct_200
private theorem cert04_fresh_198 : !cert04_U_199.contains [4, 6, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_198 : distinct cert04_U_198 = true :=
  cert04_distinct_cons [4, 6, 15, 19] cert04_U_199 cert04_fresh_198 cert04_distinct_199
private theorem cert04_fresh_197 : !cert04_U_198.contains [4, 6, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_197 : distinct cert04_U_197 = true :=
  cert04_distinct_cons [4, 6, 18, 19] cert04_U_198 cert04_fresh_197 cert04_distinct_198
private theorem cert04_fresh_196 : !cert04_U_197.contains [4, 6, 19] = true := by decide +kernel
private theorem cert04_distinct_196 : distinct cert04_U_196 = true :=
  cert04_distinct_cons [4, 6, 19] cert04_U_197 cert04_fresh_196 cert04_distinct_197
private theorem cert04_fresh_195 : !cert04_U_196.contains [4, 6, 18] = true := by decide +kernel
private theorem cert04_distinct_195 : distinct cert04_U_195 = true :=
  cert04_distinct_cons [4, 6, 18] cert04_U_196 cert04_fresh_195 cert04_distinct_196
private theorem cert04_fresh_194 : !cert04_U_195.contains [4, 6, 15] = true := by decide +kernel
private theorem cert04_distinct_194 : distinct cert04_U_194 = true :=
  cert04_distinct_cons [4, 6, 15] cert04_U_195 cert04_fresh_194 cert04_distinct_195
private theorem cert04_fresh_193 : !cert04_U_194.contains [4, 6, 14] = true := by decide +kernel
private theorem cert04_distinct_193 : distinct cert04_U_193 = true :=
  cert04_distinct_cons [4, 6, 14] cert04_U_194 cert04_fresh_193 cert04_distinct_194
private theorem cert04_fresh_192 : !cert04_U_193.contains [4, 6, 7] = true := by decide +kernel
private theorem cert04_distinct_192 : distinct cert04_U_192 = true :=
  cert04_distinct_cons [4, 6, 7] cert04_U_193 cert04_fresh_192 cert04_distinct_193
private theorem cert04_fresh_191 : !cert04_U_192.contains [4, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_191 : distinct cert04_U_191 = true :=
  cert04_distinct_cons [4, 7, 15, 19] cert04_U_192 cert04_fresh_191 cert04_distinct_192
private theorem cert04_fresh_190 : !cert04_U_191.contains [4, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_190 : distinct cert04_U_190 = true :=
  cert04_distinct_cons [4, 7, 18, 19] cert04_U_191 cert04_fresh_190 cert04_distinct_191
private theorem cert04_fresh_189 : !cert04_U_190.contains [4, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_189 : distinct cert04_U_189 = true :=
  cert04_distinct_cons [4, 7, 19] cert04_U_190 cert04_fresh_189 cert04_distinct_190
private theorem cert04_fresh_188 : !cert04_U_189.contains [4, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_188 : distinct cert04_U_188 = true :=
  cert04_distinct_cons [4, 7, 18] cert04_U_189 cert04_fresh_188 cert04_distinct_189
private theorem cert04_fresh_187 : !cert04_U_188.contains [4, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_187 : distinct cert04_U_187 = true :=
  cert04_distinct_cons [4, 7, 15] cert04_U_188 cert04_fresh_187 cert04_distinct_188
private theorem cert04_fresh_186 : !cert04_U_187.contains [4, 12, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_186 : distinct cert04_U_186 = true :=
  cert04_distinct_cons [4, 12, 13, 15, 19] cert04_U_187 cert04_fresh_186 cert04_distinct_187
private theorem cert04_fresh_185 : !cert04_U_186.contains [4, 12, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_185 : distinct cert04_U_185 = true :=
  cert04_distinct_cons [4, 12, 13, 19] cert04_U_186 cert04_fresh_185 cert04_distinct_186
private theorem cert04_fresh_184 : !cert04_U_185.contains [4, 12, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_184 : distinct cert04_U_184 = true :=
  cert04_distinct_cons [4, 12, 13, 15] cert04_U_185 cert04_fresh_184 cert04_distinct_185
private theorem cert04_fresh_183 : !cert04_U_184.contains [4, 12, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_183 : distinct cert04_U_183 = true :=
  cert04_distinct_cons [4, 12, 14, 15, 19] cert04_U_184 cert04_fresh_183 cert04_distinct_184
private theorem cert04_fresh_182 : !cert04_U_183.contains [4, 12, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_182 : distinct cert04_U_182 = true :=
  cert04_distinct_cons [4, 12, 14, 19] cert04_U_183 cert04_fresh_182 cert04_distinct_183
private theorem cert04_fresh_181 : !cert04_U_182.contains [4, 12, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_181 : distinct cert04_U_181 = true :=
  cert04_distinct_cons [4, 12, 14, 15] cert04_U_182 cert04_fresh_181 cert04_distinct_182
private theorem cert04_fresh_180 : !cert04_U_181.contains [4, 12, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_180 : distinct cert04_U_180 = true :=
  cert04_distinct_cons [4, 12, 15, 19] cert04_U_181 cert04_fresh_180 cert04_distinct_181
private theorem cert04_fresh_179 : !cert04_U_180.contains [4, 12, 19] = true := by decide +kernel
private theorem cert04_distinct_179 : distinct cert04_U_179 = true :=
  cert04_distinct_cons [4, 12, 19] cert04_U_180 cert04_fresh_179 cert04_distinct_180
private theorem cert04_fresh_178 : !cert04_U_179.contains [4, 12, 15] = true := by decide +kernel
private theorem cert04_distinct_178 : distinct cert04_U_178 = true :=
  cert04_distinct_cons [4, 12, 15] cert04_U_179 cert04_fresh_178 cert04_distinct_179
private theorem cert04_fresh_177 : !cert04_U_178.contains [4, 12, 14] = true := by decide +kernel
private theorem cert04_distinct_177 : distinct cert04_U_177 = true :=
  cert04_distinct_cons [4, 12, 14] cert04_U_178 cert04_fresh_177 cert04_distinct_178
private theorem cert04_fresh_176 : !cert04_U_177.contains [4, 12, 13] = true := by decide +kernel
private theorem cert04_distinct_176 : distinct cert04_U_176 = true :=
  cert04_distinct_cons [4, 12, 13] cert04_U_177 cert04_fresh_176 cert04_distinct_177
private theorem cert04_fresh_175 : !cert04_U_176.contains [4, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_175 : distinct cert04_U_175 = true :=
  cert04_distinct_cons [4, 13, 15, 19] cert04_U_176 cert04_fresh_175 cert04_distinct_176
private theorem cert04_fresh_174 : !cert04_U_175.contains [4, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_174 : distinct cert04_U_174 = true :=
  cert04_distinct_cons [4, 13, 19] cert04_U_175 cert04_fresh_174 cert04_distinct_175
private theorem cert04_fresh_173 : !cert04_U_174.contains [4, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_173 : distinct cert04_U_173 = true :=
  cert04_distinct_cons [4, 13, 15] cert04_U_174 cert04_fresh_173 cert04_distinct_174
private theorem cert04_fresh_172 : !cert04_U_173.contains [4, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_172 : distinct cert04_U_172 = true :=
  cert04_distinct_cons [4, 14, 15, 19] cert04_U_173 cert04_fresh_172 cert04_distinct_173
private theorem cert04_fresh_171 : !cert04_U_172.contains [4, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_171 : distinct cert04_U_171 = true :=
  cert04_distinct_cons [4, 14, 19] cert04_U_172 cert04_fresh_171 cert04_distinct_172
private theorem cert04_fresh_170 : !cert04_U_171.contains [4, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_170 : distinct cert04_U_170 = true :=
  cert04_distinct_cons [4, 14, 15] cert04_U_171 cert04_fresh_170 cert04_distinct_171
private theorem cert04_fresh_169 : !cert04_U_170.contains [4, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_169 : distinct cert04_U_169 = true :=
  cert04_distinct_cons [4, 15, 19] cert04_U_170 cert04_fresh_169 cert04_distinct_170
private theorem cert04_fresh_168 : !cert04_U_169.contains [4, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_168 : distinct cert04_U_168 = true :=
  cert04_distinct_cons [4, 18, 19] cert04_U_169 cert04_fresh_168 cert04_distinct_169
private theorem cert04_fresh_167 : !cert04_U_168.contains [4, 19] = true := by decide +kernel
private theorem cert04_distinct_167 : distinct cert04_U_167 = true :=
  cert04_distinct_cons [4, 19] cert04_U_168 cert04_fresh_167 cert04_distinct_168
private theorem cert04_fresh_166 : !cert04_U_167.contains [4, 18] = true := by decide +kernel
private theorem cert04_distinct_166 : distinct cert04_U_166 = true :=
  cert04_distinct_cons [4, 18] cert04_U_167 cert04_fresh_166 cert04_distinct_167
private theorem cert04_fresh_165 : !cert04_U_166.contains [4, 15] = true := by decide +kernel
private theorem cert04_distinct_165 : distinct cert04_U_165 = true :=
  cert04_distinct_cons [4, 15] cert04_U_166 cert04_fresh_165 cert04_distinct_166
private theorem cert04_fresh_164 : !cert04_U_165.contains [4, 14] = true := by decide +kernel
private theorem cert04_distinct_164 : distinct cert04_U_164 = true :=
  cert04_distinct_cons [4, 14] cert04_U_165 cert04_fresh_164 cert04_distinct_165
private theorem cert04_fresh_163 : !cert04_U_164.contains [4, 13] = true := by decide +kernel
private theorem cert04_distinct_163 : distinct cert04_U_163 = true :=
  cert04_distinct_cons [4, 13] cert04_U_164 cert04_fresh_163 cert04_distinct_164
private theorem cert04_fresh_162 : !cert04_U_163.contains [4, 12] = true := by decide +kernel
private theorem cert04_distinct_162 : distinct cert04_U_162 = true :=
  cert04_distinct_cons [4, 12] cert04_U_163 cert04_fresh_162 cert04_distinct_163
private theorem cert04_fresh_161 : !cert04_U_162.contains [4, 7] = true := by decide +kernel
private theorem cert04_distinct_161 : distinct cert04_U_161 = true :=
  cert04_distinct_cons [4, 7] cert04_U_162 cert04_fresh_161 cert04_distinct_162
private theorem cert04_fresh_160 : !cert04_U_161.contains [4, 6] = true := by decide +kernel
private theorem cert04_distinct_160 : distinct cert04_U_160 = true :=
  cert04_distinct_cons [4, 6] cert04_U_161 cert04_fresh_160 cert04_distinct_161
private theorem cert04_fresh_159 : !cert04_U_160.contains [4, 5] = true := by decide +kernel
private theorem cert04_distinct_159 : distinct cert04_U_159 = true :=
  cert04_distinct_cons [4, 5] cert04_U_160 cert04_fresh_159 cert04_distinct_160
private theorem cert04_fresh_158 : !cert04_U_159.contains [5, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_158 : distinct cert04_U_158 = true :=
  cert04_distinct_cons [5, 7, 15, 19] cert04_U_159 cert04_fresh_158 cert04_distinct_159
private theorem cert04_fresh_157 : !cert04_U_158.contains [5, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_157 : distinct cert04_U_157 = true :=
  cert04_distinct_cons [5, 7, 18, 19] cert04_U_158 cert04_fresh_157 cert04_distinct_158
private theorem cert04_fresh_156 : !cert04_U_157.contains [5, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_156 : distinct cert04_U_156 = true :=
  cert04_distinct_cons [5, 7, 19] cert04_U_157 cert04_fresh_156 cert04_distinct_157
private theorem cert04_fresh_155 : !cert04_U_156.contains [5, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_155 : distinct cert04_U_155 = true :=
  cert04_distinct_cons [5, 7, 18] cert04_U_156 cert04_fresh_155 cert04_distinct_156
private theorem cert04_fresh_154 : !cert04_U_155.contains [5, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_154 : distinct cert04_U_154 = true :=
  cert04_distinct_cons [5, 7, 15] cert04_U_155 cert04_fresh_154 cert04_distinct_155
private theorem cert04_fresh_153 : !cert04_U_154.contains [5, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_153 : distinct cert04_U_153 = true :=
  cert04_distinct_cons [5, 13, 15, 19] cert04_U_154 cert04_fresh_153 cert04_distinct_154
private theorem cert04_fresh_152 : !cert04_U_153.contains [5, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_152 : distinct cert04_U_152 = true :=
  cert04_distinct_cons [5, 13, 19] cert04_U_153 cert04_fresh_152 cert04_distinct_153
private theorem cert04_fresh_151 : !cert04_U_152.contains [5, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_151 : distinct cert04_U_151 = true :=
  cert04_distinct_cons [5, 13, 15] cert04_U_152 cert04_fresh_151 cert04_distinct_152
private theorem cert04_fresh_150 : !cert04_U_151.contains [5, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_150 : distinct cert04_U_150 = true :=
  cert04_distinct_cons [5, 15, 19] cert04_U_151 cert04_fresh_150 cert04_distinct_151
private theorem cert04_fresh_149 : !cert04_U_150.contains [5, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_149 : distinct cert04_U_149 = true :=
  cert04_distinct_cons [5, 18, 19] cert04_U_150 cert04_fresh_149 cert04_distinct_150
private theorem cert04_fresh_148 : !cert04_U_149.contains [5, 19] = true := by decide +kernel
private theorem cert04_distinct_148 : distinct cert04_U_148 = true :=
  cert04_distinct_cons [5, 19] cert04_U_149 cert04_fresh_148 cert04_distinct_149
private theorem cert04_fresh_147 : !cert04_U_148.contains [5, 18] = true := by decide +kernel
private theorem cert04_distinct_147 : distinct cert04_U_147 = true :=
  cert04_distinct_cons [5, 18] cert04_U_148 cert04_fresh_147 cert04_distinct_148
private theorem cert04_fresh_146 : !cert04_U_147.contains [5, 15] = true := by decide +kernel
private theorem cert04_distinct_146 : distinct cert04_U_146 = true :=
  cert04_distinct_cons [5, 15] cert04_U_147 cert04_fresh_146 cert04_distinct_147
private theorem cert04_fresh_145 : !cert04_U_146.contains [5, 13] = true := by decide +kernel
private theorem cert04_distinct_145 : distinct cert04_U_145 = true :=
  cert04_distinct_cons [5, 13] cert04_U_146 cert04_fresh_145 cert04_distinct_146
private theorem cert04_fresh_144 : !cert04_U_145.contains [5, 7] = true := by decide +kernel
private theorem cert04_distinct_144 : distinct cert04_U_144 = true :=
  cert04_distinct_cons [5, 7] cert04_U_145 cert04_fresh_144 cert04_distinct_145
private theorem cert04_fresh_143 : !cert04_U_144.contains [6, 7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_143 : distinct cert04_U_143 = true :=
  cert04_distinct_cons [6, 7, 15, 19] cert04_U_144 cert04_fresh_143 cert04_distinct_144
private theorem cert04_fresh_142 : !cert04_U_143.contains [6, 7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_142 : distinct cert04_U_142 = true :=
  cert04_distinct_cons [6, 7, 18, 19] cert04_U_143 cert04_fresh_142 cert04_distinct_143
private theorem cert04_fresh_141 : !cert04_U_142.contains [6, 7, 19] = true := by decide +kernel
private theorem cert04_distinct_141 : distinct cert04_U_141 = true :=
  cert04_distinct_cons [6, 7, 19] cert04_U_142 cert04_fresh_141 cert04_distinct_142
private theorem cert04_fresh_140 : !cert04_U_141.contains [6, 7, 18] = true := by decide +kernel
private theorem cert04_distinct_140 : distinct cert04_U_140 = true :=
  cert04_distinct_cons [6, 7, 18] cert04_U_141 cert04_fresh_140 cert04_distinct_141
private theorem cert04_fresh_139 : !cert04_U_140.contains [6, 7, 15] = true := by decide +kernel
private theorem cert04_distinct_139 : distinct cert04_U_139 = true :=
  cert04_distinct_cons [6, 7, 15] cert04_U_140 cert04_fresh_139 cert04_distinct_140
private theorem cert04_fresh_138 : !cert04_U_139.contains [6, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_138 : distinct cert04_U_138 = true :=
  cert04_distinct_cons [6, 14, 15, 19] cert04_U_139 cert04_fresh_138 cert04_distinct_139
private theorem cert04_fresh_137 : !cert04_U_138.contains [6, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_137 : distinct cert04_U_137 = true :=
  cert04_distinct_cons [6, 14, 19] cert04_U_138 cert04_fresh_137 cert04_distinct_138
private theorem cert04_fresh_136 : !cert04_U_137.contains [6, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_136 : distinct cert04_U_136 = true :=
  cert04_distinct_cons [6, 14, 15] cert04_U_137 cert04_fresh_136 cert04_distinct_137
private theorem cert04_fresh_135 : !cert04_U_136.contains [6, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_135 : distinct cert04_U_135 = true :=
  cert04_distinct_cons [6, 15, 19] cert04_U_136 cert04_fresh_135 cert04_distinct_136
private theorem cert04_fresh_134 : !cert04_U_135.contains [6, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_134 : distinct cert04_U_134 = true :=
  cert04_distinct_cons [6, 18, 19] cert04_U_135 cert04_fresh_134 cert04_distinct_135
private theorem cert04_fresh_133 : !cert04_U_134.contains [6, 19] = true := by decide +kernel
private theorem cert04_distinct_133 : distinct cert04_U_133 = true :=
  cert04_distinct_cons [6, 19] cert04_U_134 cert04_fresh_133 cert04_distinct_134
private theorem cert04_fresh_132 : !cert04_U_133.contains [6, 18] = true := by decide +kernel
private theorem cert04_distinct_132 : distinct cert04_U_132 = true :=
  cert04_distinct_cons [6, 18] cert04_U_133 cert04_fresh_132 cert04_distinct_133
private theorem cert04_fresh_131 : !cert04_U_132.contains [6, 15] = true := by decide +kernel
private theorem cert04_distinct_131 : distinct cert04_U_131 = true :=
  cert04_distinct_cons [6, 15] cert04_U_132 cert04_fresh_131 cert04_distinct_132
private theorem cert04_fresh_130 : !cert04_U_131.contains [6, 14] = true := by decide +kernel
private theorem cert04_distinct_130 : distinct cert04_U_130 = true :=
  cert04_distinct_cons [6, 14] cert04_U_131 cert04_fresh_130 cert04_distinct_131
private theorem cert04_fresh_129 : !cert04_U_130.contains [6, 7] = true := by decide +kernel
private theorem cert04_distinct_129 : distinct cert04_U_129 = true :=
  cert04_distinct_cons [6, 7] cert04_U_130 cert04_fresh_129 cert04_distinct_130
private theorem cert04_fresh_128 : !cert04_U_129.contains [7, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_128 : distinct cert04_U_128 = true :=
  cert04_distinct_cons [7, 15, 19] cert04_U_129 cert04_fresh_128 cert04_distinct_129
private theorem cert04_fresh_127 : !cert04_U_128.contains [7, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_127 : distinct cert04_U_127 = true :=
  cert04_distinct_cons [7, 18, 19] cert04_U_128 cert04_fresh_127 cert04_distinct_128
private theorem cert04_fresh_126 : !cert04_U_127.contains [7, 19] = true := by decide +kernel
private theorem cert04_distinct_126 : distinct cert04_U_126 = true :=
  cert04_distinct_cons [7, 19] cert04_U_127 cert04_fresh_126 cert04_distinct_127
private theorem cert04_fresh_125 : !cert04_U_126.contains [7, 18] = true := by decide +kernel
private theorem cert04_distinct_125 : distinct cert04_U_125 = true :=
  cert04_distinct_cons [7, 18] cert04_U_126 cert04_fresh_125 cert04_distinct_126
private theorem cert04_fresh_124 : !cert04_U_125.contains [7, 15] = true := by decide +kernel
private theorem cert04_distinct_124 : distinct cert04_U_124 = true :=
  cert04_distinct_cons [7, 15] cert04_U_125 cert04_fresh_124 cert04_distinct_125
private theorem cert04_fresh_123 : !cert04_U_124.contains [8, 9, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_123 : distinct cert04_U_123 = true :=
  cert04_distinct_cons [8, 9, 11, 15, 19] cert04_U_124 cert04_fresh_123 cert04_distinct_124
private theorem cert04_fresh_122 : !cert04_U_123.contains [8, 9, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_122 : distinct cert04_U_122 = true :=
  cert04_distinct_cons [8, 9, 11, 19] cert04_U_123 cert04_fresh_122 cert04_distinct_123
private theorem cert04_fresh_121 : !cert04_U_122.contains [8, 9, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_121 : distinct cert04_U_121 = true :=
  cert04_distinct_cons [8, 9, 11, 15] cert04_U_122 cert04_fresh_121 cert04_distinct_122
private theorem cert04_fresh_120 : !cert04_U_121.contains [8, 9, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_120 : distinct cert04_U_120 = true :=
  cert04_distinct_cons [8, 9, 13, 15, 19] cert04_U_121 cert04_fresh_120 cert04_distinct_121
private theorem cert04_fresh_119 : !cert04_U_120.contains [8, 9, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_119 : distinct cert04_U_119 = true :=
  cert04_distinct_cons [8, 9, 13, 19] cert04_U_120 cert04_fresh_119 cert04_distinct_120
private theorem cert04_fresh_118 : !cert04_U_119.contains [8, 9, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_118 : distinct cert04_U_118 = true :=
  cert04_distinct_cons [8, 9, 13, 15] cert04_U_119 cert04_fresh_118 cert04_distinct_119
private theorem cert04_fresh_117 : !cert04_U_118.contains [8, 9, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_117 : distinct cert04_U_117 = true :=
  cert04_distinct_cons [8, 9, 15, 19] cert04_U_118 cert04_fresh_117 cert04_distinct_118
private theorem cert04_fresh_116 : !cert04_U_117.contains [8, 9, 19] = true := by decide +kernel
private theorem cert04_distinct_116 : distinct cert04_U_116 = true :=
  cert04_distinct_cons [8, 9, 19] cert04_U_117 cert04_fresh_116 cert04_distinct_117
private theorem cert04_fresh_115 : !cert04_U_116.contains [8, 9, 15] = true := by decide +kernel
private theorem cert04_distinct_115 : distinct cert04_U_115 = true :=
  cert04_distinct_cons [8, 9, 15] cert04_U_116 cert04_fresh_115 cert04_distinct_116
private theorem cert04_fresh_114 : !cert04_U_115.contains [8, 9, 13] = true := by decide +kernel
private theorem cert04_distinct_114 : distinct cert04_U_114 = true :=
  cert04_distinct_cons [8, 9, 13] cert04_U_115 cert04_fresh_114 cert04_distinct_115
private theorem cert04_fresh_113 : !cert04_U_114.contains [8, 9, 11] = true := by decide +kernel
private theorem cert04_distinct_113 : distinct cert04_U_113 = true :=
  cert04_distinct_cons [8, 9, 11] cert04_U_114 cert04_fresh_113 cert04_distinct_114
private theorem cert04_fresh_112 : !cert04_U_113.contains [8, 10, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_112 : distinct cert04_U_112 = true :=
  cert04_distinct_cons [8, 10, 11, 15, 19] cert04_U_113 cert04_fresh_112 cert04_distinct_113
private theorem cert04_fresh_111 : !cert04_U_112.contains [8, 10, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_111 : distinct cert04_U_111 = true :=
  cert04_distinct_cons [8, 10, 11, 19] cert04_U_112 cert04_fresh_111 cert04_distinct_112
private theorem cert04_fresh_110 : !cert04_U_111.contains [8, 10, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_110 : distinct cert04_U_110 = true :=
  cert04_distinct_cons [8, 10, 11, 15] cert04_U_111 cert04_fresh_110 cert04_distinct_111
private theorem cert04_fresh_109 : !cert04_U_110.contains [8, 10, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_109 : distinct cert04_U_109 = true :=
  cert04_distinct_cons [8, 10, 14, 15, 19] cert04_U_110 cert04_fresh_109 cert04_distinct_110
private theorem cert04_fresh_108 : !cert04_U_109.contains [8, 10, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_108 : distinct cert04_U_108 = true :=
  cert04_distinct_cons [8, 10, 14, 19] cert04_U_109 cert04_fresh_108 cert04_distinct_109
private theorem cert04_fresh_107 : !cert04_U_108.contains [8, 10, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_107 : distinct cert04_U_107 = true :=
  cert04_distinct_cons [8, 10, 14, 15] cert04_U_108 cert04_fresh_107 cert04_distinct_108
private theorem cert04_fresh_106 : !cert04_U_107.contains [8, 10, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_106 : distinct cert04_U_106 = true :=
  cert04_distinct_cons [8, 10, 15, 19] cert04_U_107 cert04_fresh_106 cert04_distinct_107
private theorem cert04_fresh_105 : !cert04_U_106.contains [8, 10, 19] = true := by decide +kernel
private theorem cert04_distinct_105 : distinct cert04_U_105 = true :=
  cert04_distinct_cons [8, 10, 19] cert04_U_106 cert04_fresh_105 cert04_distinct_106
private theorem cert04_fresh_104 : !cert04_U_105.contains [8, 10, 15] = true := by decide +kernel
private theorem cert04_distinct_104 : distinct cert04_U_104 = true :=
  cert04_distinct_cons [8, 10, 15] cert04_U_105 cert04_fresh_104 cert04_distinct_105
private theorem cert04_fresh_103 : !cert04_U_104.contains [8, 10, 14] = true := by decide +kernel
private theorem cert04_distinct_103 : distinct cert04_U_103 = true :=
  cert04_distinct_cons [8, 10, 14] cert04_U_104 cert04_fresh_103 cert04_distinct_104
private theorem cert04_fresh_102 : !cert04_U_103.contains [8, 10, 11] = true := by decide +kernel
private theorem cert04_distinct_102 : distinct cert04_U_102 = true :=
  cert04_distinct_cons [8, 10, 11] cert04_U_103 cert04_fresh_102 cert04_distinct_103
private theorem cert04_fresh_101 : !cert04_U_102.contains [8, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_101 : distinct cert04_U_101 = true :=
  cert04_distinct_cons [8, 11, 15, 19] cert04_U_102 cert04_fresh_101 cert04_distinct_102
private theorem cert04_fresh_100 : !cert04_U_101.contains [8, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_100 : distinct cert04_U_100 = true :=
  cert04_distinct_cons [8, 11, 19] cert04_U_101 cert04_fresh_100 cert04_distinct_101
private theorem cert04_fresh_99 : !cert04_U_100.contains [8, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_99 : distinct cert04_U_99 = true :=
  cert04_distinct_cons [8, 11, 15] cert04_U_100 cert04_fresh_99 cert04_distinct_100
private theorem cert04_fresh_98 : !cert04_U_99.contains [8, 12, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_98 : distinct cert04_U_98 = true :=
  cert04_distinct_cons [8, 12, 13, 15, 19] cert04_U_99 cert04_fresh_98 cert04_distinct_99
private theorem cert04_fresh_97 : !cert04_U_98.contains [8, 12, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_97 : distinct cert04_U_97 = true :=
  cert04_distinct_cons [8, 12, 13, 19] cert04_U_98 cert04_fresh_97 cert04_distinct_98
private theorem cert04_fresh_96 : !cert04_U_97.contains [8, 12, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_96 : distinct cert04_U_96 = true :=
  cert04_distinct_cons [8, 12, 13, 15] cert04_U_97 cert04_fresh_96 cert04_distinct_97
private theorem cert04_fresh_95 : !cert04_U_96.contains [8, 12, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_95 : distinct cert04_U_95 = true :=
  cert04_distinct_cons [8, 12, 14, 15, 19] cert04_U_96 cert04_fresh_95 cert04_distinct_96
private theorem cert04_fresh_94 : !cert04_U_95.contains [8, 12, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_94 : distinct cert04_U_94 = true :=
  cert04_distinct_cons [8, 12, 14, 19] cert04_U_95 cert04_fresh_94 cert04_distinct_95
private theorem cert04_fresh_93 : !cert04_U_94.contains [8, 12, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_93 : distinct cert04_U_93 = true :=
  cert04_distinct_cons [8, 12, 14, 15] cert04_U_94 cert04_fresh_93 cert04_distinct_94
private theorem cert04_fresh_92 : !cert04_U_93.contains [8, 12, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_92 : distinct cert04_U_92 = true :=
  cert04_distinct_cons [8, 12, 15, 19] cert04_U_93 cert04_fresh_92 cert04_distinct_93
private theorem cert04_fresh_91 : !cert04_U_92.contains [8, 12, 19] = true := by decide +kernel
private theorem cert04_distinct_91 : distinct cert04_U_91 = true :=
  cert04_distinct_cons [8, 12, 19] cert04_U_92 cert04_fresh_91 cert04_distinct_92
private theorem cert04_fresh_90 : !cert04_U_91.contains [8, 12, 15] = true := by decide +kernel
private theorem cert04_distinct_90 : distinct cert04_U_90 = true :=
  cert04_distinct_cons [8, 12, 15] cert04_U_91 cert04_fresh_90 cert04_distinct_91
private theorem cert04_fresh_89 : !cert04_U_90.contains [8, 12, 14] = true := by decide +kernel
private theorem cert04_distinct_89 : distinct cert04_U_89 = true :=
  cert04_distinct_cons [8, 12, 14] cert04_U_90 cert04_fresh_89 cert04_distinct_90
private theorem cert04_fresh_88 : !cert04_U_89.contains [8, 12, 13] = true := by decide +kernel
private theorem cert04_distinct_88 : distinct cert04_U_88 = true :=
  cert04_distinct_cons [8, 12, 13] cert04_U_89 cert04_fresh_88 cert04_distinct_89
private theorem cert04_fresh_87 : !cert04_U_88.contains [8, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_87 : distinct cert04_U_87 = true :=
  cert04_distinct_cons [8, 13, 15, 19] cert04_U_88 cert04_fresh_87 cert04_distinct_88
private theorem cert04_fresh_86 : !cert04_U_87.contains [8, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_86 : distinct cert04_U_86 = true :=
  cert04_distinct_cons [8, 13, 19] cert04_U_87 cert04_fresh_86 cert04_distinct_87
private theorem cert04_fresh_85 : !cert04_U_86.contains [8, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_85 : distinct cert04_U_85 = true :=
  cert04_distinct_cons [8, 13, 15] cert04_U_86 cert04_fresh_85 cert04_distinct_86
private theorem cert04_fresh_84 : !cert04_U_85.contains [8, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_84 : distinct cert04_U_84 = true :=
  cert04_distinct_cons [8, 14, 15, 19] cert04_U_85 cert04_fresh_84 cert04_distinct_85
private theorem cert04_fresh_83 : !cert04_U_84.contains [8, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_83 : distinct cert04_U_83 = true :=
  cert04_distinct_cons [8, 14, 19] cert04_U_84 cert04_fresh_83 cert04_distinct_84
private theorem cert04_fresh_82 : !cert04_U_83.contains [8, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_82 : distinct cert04_U_82 = true :=
  cert04_distinct_cons [8, 14, 15] cert04_U_83 cert04_fresh_82 cert04_distinct_83
private theorem cert04_fresh_81 : !cert04_U_82.contains [8, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_81 : distinct cert04_U_81 = true :=
  cert04_distinct_cons [8, 15, 19] cert04_U_82 cert04_fresh_81 cert04_distinct_82
private theorem cert04_fresh_80 : !cert04_U_81.contains [8, 19] = true := by decide +kernel
private theorem cert04_distinct_80 : distinct cert04_U_80 = true :=
  cert04_distinct_cons [8, 19] cert04_U_81 cert04_fresh_80 cert04_distinct_81
private theorem cert04_fresh_79 : !cert04_U_80.contains [8, 15] = true := by decide +kernel
private theorem cert04_distinct_79 : distinct cert04_U_79 = true :=
  cert04_distinct_cons [8, 15] cert04_U_80 cert04_fresh_79 cert04_distinct_80
private theorem cert04_fresh_78 : !cert04_U_79.contains [8, 14] = true := by decide +kernel
private theorem cert04_distinct_78 : distinct cert04_U_78 = true :=
  cert04_distinct_cons [8, 14] cert04_U_79 cert04_fresh_78 cert04_distinct_79
private theorem cert04_fresh_77 : !cert04_U_78.contains [8, 13] = true := by decide +kernel
private theorem cert04_distinct_77 : distinct cert04_U_77 = true :=
  cert04_distinct_cons [8, 13] cert04_U_78 cert04_fresh_77 cert04_distinct_78
private theorem cert04_fresh_76 : !cert04_U_77.contains [8, 12] = true := by decide +kernel
private theorem cert04_distinct_76 : distinct cert04_U_76 = true :=
  cert04_distinct_cons [8, 12] cert04_U_77 cert04_fresh_76 cert04_distinct_77
private theorem cert04_fresh_75 : !cert04_U_76.contains [8, 11] = true := by decide +kernel
private theorem cert04_distinct_75 : distinct cert04_U_75 = true :=
  cert04_distinct_cons [8, 11] cert04_U_76 cert04_fresh_75 cert04_distinct_76
private theorem cert04_fresh_74 : !cert04_U_75.contains [8, 10] = true := by decide +kernel
private theorem cert04_distinct_74 : distinct cert04_U_74 = true :=
  cert04_distinct_cons [8, 10] cert04_U_75 cert04_fresh_74 cert04_distinct_75
private theorem cert04_fresh_73 : !cert04_U_74.contains [8, 9] = true := by decide +kernel
private theorem cert04_distinct_73 : distinct cert04_U_73 = true :=
  cert04_distinct_cons [8, 9] cert04_U_74 cert04_fresh_73 cert04_distinct_74
private theorem cert04_fresh_72 : !cert04_U_73.contains [9, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_72 : distinct cert04_U_72 = true :=
  cert04_distinct_cons [9, 11, 15, 19] cert04_U_73 cert04_fresh_72 cert04_distinct_73
private theorem cert04_fresh_71 : !cert04_U_72.contains [9, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_71 : distinct cert04_U_71 = true :=
  cert04_distinct_cons [9, 11, 19] cert04_U_72 cert04_fresh_71 cert04_distinct_72
private theorem cert04_fresh_70 : !cert04_U_71.contains [9, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_70 : distinct cert04_U_70 = true :=
  cert04_distinct_cons [9, 11, 15] cert04_U_71 cert04_fresh_70 cert04_distinct_71
private theorem cert04_fresh_69 : !cert04_U_70.contains [9, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_69 : distinct cert04_U_69 = true :=
  cert04_distinct_cons [9, 13, 15, 19] cert04_U_70 cert04_fresh_69 cert04_distinct_70
private theorem cert04_fresh_68 : !cert04_U_69.contains [9, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_68 : distinct cert04_U_68 = true :=
  cert04_distinct_cons [9, 13, 19] cert04_U_69 cert04_fresh_68 cert04_distinct_69
private theorem cert04_fresh_67 : !cert04_U_68.contains [9, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_67 : distinct cert04_U_67 = true :=
  cert04_distinct_cons [9, 13, 15] cert04_U_68 cert04_fresh_67 cert04_distinct_68
private theorem cert04_fresh_66 : !cert04_U_67.contains [9, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_66 : distinct cert04_U_66 = true :=
  cert04_distinct_cons [9, 15, 19] cert04_U_67 cert04_fresh_66 cert04_distinct_67
private theorem cert04_fresh_65 : !cert04_U_66.contains [9, 19] = true := by decide +kernel
private theorem cert04_distinct_65 : distinct cert04_U_65 = true :=
  cert04_distinct_cons [9, 19] cert04_U_66 cert04_fresh_65 cert04_distinct_66
private theorem cert04_fresh_64 : !cert04_U_65.contains [9, 15] = true := by decide +kernel
private theorem cert04_distinct_64 : distinct cert04_U_64 = true :=
  cert04_distinct_cons [9, 15] cert04_U_65 cert04_fresh_64 cert04_distinct_65
private theorem cert04_fresh_63 : !cert04_U_64.contains [9, 13] = true := by decide +kernel
private theorem cert04_distinct_63 : distinct cert04_U_63 = true :=
  cert04_distinct_cons [9, 13] cert04_U_64 cert04_fresh_63 cert04_distinct_64
private theorem cert04_fresh_62 : !cert04_U_63.contains [9, 11] = true := by decide +kernel
private theorem cert04_distinct_62 : distinct cert04_U_62 = true :=
  cert04_distinct_cons [9, 11] cert04_U_63 cert04_fresh_62 cert04_distinct_63
private theorem cert04_fresh_61 : !cert04_U_62.contains [10, 11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_61 : distinct cert04_U_61 = true :=
  cert04_distinct_cons [10, 11, 15, 19] cert04_U_62 cert04_fresh_61 cert04_distinct_62
private theorem cert04_fresh_60 : !cert04_U_61.contains [10, 11, 19] = true := by decide +kernel
private theorem cert04_distinct_60 : distinct cert04_U_60 = true :=
  cert04_distinct_cons [10, 11, 19] cert04_U_61 cert04_fresh_60 cert04_distinct_61
private theorem cert04_fresh_59 : !cert04_U_60.contains [10, 11, 15] = true := by decide +kernel
private theorem cert04_distinct_59 : distinct cert04_U_59 = true :=
  cert04_distinct_cons [10, 11, 15] cert04_U_60 cert04_fresh_59 cert04_distinct_60
private theorem cert04_fresh_58 : !cert04_U_59.contains [10, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_58 : distinct cert04_U_58 = true :=
  cert04_distinct_cons [10, 14, 15, 19] cert04_U_59 cert04_fresh_58 cert04_distinct_59
private theorem cert04_fresh_57 : !cert04_U_58.contains [10, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_57 : distinct cert04_U_57 = true :=
  cert04_distinct_cons [10, 14, 19] cert04_U_58 cert04_fresh_57 cert04_distinct_58
private theorem cert04_fresh_56 : !cert04_U_57.contains [10, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_56 : distinct cert04_U_56 = true :=
  cert04_distinct_cons [10, 14, 15] cert04_U_57 cert04_fresh_56 cert04_distinct_57
private theorem cert04_fresh_55 : !cert04_U_56.contains [10, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_55 : distinct cert04_U_55 = true :=
  cert04_distinct_cons [10, 15, 19] cert04_U_56 cert04_fresh_55 cert04_distinct_56
private theorem cert04_fresh_54 : !cert04_U_55.contains [10, 19] = true := by decide +kernel
private theorem cert04_distinct_54 : distinct cert04_U_54 = true :=
  cert04_distinct_cons [10, 19] cert04_U_55 cert04_fresh_54 cert04_distinct_55
private theorem cert04_fresh_53 : !cert04_U_54.contains [10, 15] = true := by decide +kernel
private theorem cert04_distinct_53 : distinct cert04_U_53 = true :=
  cert04_distinct_cons [10, 15] cert04_U_54 cert04_fresh_53 cert04_distinct_54
private theorem cert04_fresh_52 : !cert04_U_53.contains [10, 14] = true := by decide +kernel
private theorem cert04_distinct_52 : distinct cert04_U_52 = true :=
  cert04_distinct_cons [10, 14] cert04_U_53 cert04_fresh_52 cert04_distinct_53
private theorem cert04_fresh_51 : !cert04_U_52.contains [10, 11] = true := by decide +kernel
private theorem cert04_distinct_51 : distinct cert04_U_51 = true :=
  cert04_distinct_cons [10, 11] cert04_U_52 cert04_fresh_51 cert04_distinct_52
private theorem cert04_fresh_50 : !cert04_U_51.contains [11, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_50 : distinct cert04_U_50 = true :=
  cert04_distinct_cons [11, 15, 19] cert04_U_51 cert04_fresh_50 cert04_distinct_51
private theorem cert04_fresh_49 : !cert04_U_50.contains [11, 19] = true := by decide +kernel
private theorem cert04_distinct_49 : distinct cert04_U_49 = true :=
  cert04_distinct_cons [11, 19] cert04_U_50 cert04_fresh_49 cert04_distinct_50
private theorem cert04_fresh_48 : !cert04_U_49.contains [11, 15] = true := by decide +kernel
private theorem cert04_distinct_48 : distinct cert04_U_48 = true :=
  cert04_distinct_cons [11, 15] cert04_U_49 cert04_fresh_48 cert04_distinct_49
private theorem cert04_fresh_47 : !cert04_U_48.contains [12, 13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_47 : distinct cert04_U_47 = true :=
  cert04_distinct_cons [12, 13, 15, 19] cert04_U_48 cert04_fresh_47 cert04_distinct_48
private theorem cert04_fresh_46 : !cert04_U_47.contains [12, 13, 19] = true := by decide +kernel
private theorem cert04_distinct_46 : distinct cert04_U_46 = true :=
  cert04_distinct_cons [12, 13, 19] cert04_U_47 cert04_fresh_46 cert04_distinct_47
private theorem cert04_fresh_45 : !cert04_U_46.contains [12, 13, 15] = true := by decide +kernel
private theorem cert04_distinct_45 : distinct cert04_U_45 = true :=
  cert04_distinct_cons [12, 13, 15] cert04_U_46 cert04_fresh_45 cert04_distinct_46
private theorem cert04_fresh_44 : !cert04_U_45.contains [12, 14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_44 : distinct cert04_U_44 = true :=
  cert04_distinct_cons [12, 14, 15, 19] cert04_U_45 cert04_fresh_44 cert04_distinct_45
private theorem cert04_fresh_43 : !cert04_U_44.contains [12, 14, 19] = true := by decide +kernel
private theorem cert04_distinct_43 : distinct cert04_U_43 = true :=
  cert04_distinct_cons [12, 14, 19] cert04_U_44 cert04_fresh_43 cert04_distinct_44
private theorem cert04_fresh_42 : !cert04_U_43.contains [12, 14, 15] = true := by decide +kernel
private theorem cert04_distinct_42 : distinct cert04_U_42 = true :=
  cert04_distinct_cons [12, 14, 15] cert04_U_43 cert04_fresh_42 cert04_distinct_43
private theorem cert04_fresh_41 : !cert04_U_42.contains [12, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_41 : distinct cert04_U_41 = true :=
  cert04_distinct_cons [12, 15, 19] cert04_U_42 cert04_fresh_41 cert04_distinct_42
private theorem cert04_fresh_40 : !cert04_U_41.contains [12, 19] = true := by decide +kernel
private theorem cert04_distinct_40 : distinct cert04_U_40 = true :=
  cert04_distinct_cons [12, 19] cert04_U_41 cert04_fresh_40 cert04_distinct_41
private theorem cert04_fresh_39 : !cert04_U_40.contains [12, 15] = true := by decide +kernel
private theorem cert04_distinct_39 : distinct cert04_U_39 = true :=
  cert04_distinct_cons [12, 15] cert04_U_40 cert04_fresh_39 cert04_distinct_40
private theorem cert04_fresh_38 : !cert04_U_39.contains [12, 14] = true := by decide +kernel
private theorem cert04_distinct_38 : distinct cert04_U_38 = true :=
  cert04_distinct_cons [12, 14] cert04_U_39 cert04_fresh_38 cert04_distinct_39
private theorem cert04_fresh_37 : !cert04_U_38.contains [12, 13] = true := by decide +kernel
private theorem cert04_distinct_37 : distinct cert04_U_37 = true :=
  cert04_distinct_cons [12, 13] cert04_U_38 cert04_fresh_37 cert04_distinct_38
private theorem cert04_fresh_36 : !cert04_U_37.contains [13, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_36 : distinct cert04_U_36 = true :=
  cert04_distinct_cons [13, 15, 19] cert04_U_37 cert04_fresh_36 cert04_distinct_37
private theorem cert04_fresh_35 : !cert04_U_36.contains [13, 19] = true := by decide +kernel
private theorem cert04_distinct_35 : distinct cert04_U_35 = true :=
  cert04_distinct_cons [13, 19] cert04_U_36 cert04_fresh_35 cert04_distinct_36
private theorem cert04_fresh_34 : !cert04_U_35.contains [13, 15] = true := by decide +kernel
private theorem cert04_distinct_34 : distinct cert04_U_34 = true :=
  cert04_distinct_cons [13, 15] cert04_U_35 cert04_fresh_34 cert04_distinct_35
private theorem cert04_fresh_33 : !cert04_U_34.contains [14, 15, 19] = true := by decide +kernel
private theorem cert04_distinct_33 : distinct cert04_U_33 = true :=
  cert04_distinct_cons [14, 15, 19] cert04_U_34 cert04_fresh_33 cert04_distinct_34
private theorem cert04_fresh_32 : !cert04_U_33.contains [14, 19] = true := by decide +kernel
private theorem cert04_distinct_32 : distinct cert04_U_32 = true :=
  cert04_distinct_cons [14, 19] cert04_U_33 cert04_fresh_32 cert04_distinct_33
private theorem cert04_fresh_31 : !cert04_U_32.contains [14, 15] = true := by decide +kernel
private theorem cert04_distinct_31 : distinct cert04_U_31 = true :=
  cert04_distinct_cons [14, 15] cert04_U_32 cert04_fresh_31 cert04_distinct_32
private theorem cert04_fresh_30 : !cert04_U_31.contains [15, 19] = true := by decide +kernel
private theorem cert04_distinct_30 : distinct cert04_U_30 = true :=
  cert04_distinct_cons [15, 19] cert04_U_31 cert04_fresh_30 cert04_distinct_31
private theorem cert04_fresh_29 : !cert04_U_30.contains [16, 17, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_29 : distinct cert04_U_29 = true :=
  cert04_distinct_cons [16, 17, 18, 19] cert04_U_30 cert04_fresh_29 cert04_distinct_30
private theorem cert04_fresh_28 : !cert04_U_29.contains [16, 17, 19] = true := by decide +kernel
private theorem cert04_distinct_28 : distinct cert04_U_28 = true :=
  cert04_distinct_cons [16, 17, 19] cert04_U_29 cert04_fresh_28 cert04_distinct_29
private theorem cert04_fresh_27 : !cert04_U_28.contains [16, 17, 18] = true := by decide +kernel
private theorem cert04_distinct_27 : distinct cert04_U_27 = true :=
  cert04_distinct_cons [16, 17, 18] cert04_U_28 cert04_fresh_27 cert04_distinct_28
private theorem cert04_fresh_26 : !cert04_U_27.contains [16, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_26 : distinct cert04_U_26 = true :=
  cert04_distinct_cons [16, 18, 19] cert04_U_27 cert04_fresh_26 cert04_distinct_27
private theorem cert04_fresh_25 : !cert04_U_26.contains [16, 19] = true := by decide +kernel
private theorem cert04_distinct_25 : distinct cert04_U_25 = true :=
  cert04_distinct_cons [16, 19] cert04_U_26 cert04_fresh_25 cert04_distinct_26
private theorem cert04_fresh_24 : !cert04_U_25.contains [16, 18] = true := by decide +kernel
private theorem cert04_distinct_24 : distinct cert04_U_24 = true :=
  cert04_distinct_cons [16, 18] cert04_U_25 cert04_fresh_24 cert04_distinct_25
private theorem cert04_fresh_23 : !cert04_U_24.contains [16, 17] = true := by decide +kernel
private theorem cert04_distinct_23 : distinct cert04_U_23 = true :=
  cert04_distinct_cons [16, 17] cert04_U_24 cert04_fresh_23 cert04_distinct_24
private theorem cert04_fresh_22 : !cert04_U_23.contains [17, 18, 19] = true := by decide +kernel
private theorem cert04_distinct_22 : distinct cert04_U_22 = true :=
  cert04_distinct_cons [17, 18, 19] cert04_U_23 cert04_fresh_22 cert04_distinct_23
private theorem cert04_fresh_21 : !cert04_U_22.contains [17, 19] = true := by decide +kernel
private theorem cert04_distinct_21 : distinct cert04_U_21 = true :=
  cert04_distinct_cons [17, 19] cert04_U_22 cert04_fresh_21 cert04_distinct_22
private theorem cert04_fresh_20 : !cert04_U_21.contains [17, 18] = true := by decide +kernel
private theorem cert04_distinct_20 : distinct cert04_U_20 = true :=
  cert04_distinct_cons [17, 18] cert04_U_21 cert04_fresh_20 cert04_distinct_21
private theorem cert04_fresh_19 : !cert04_U_20.contains [18, 19] = true := by decide +kernel
private theorem cert04_distinct_19 : distinct cert04_U_19 = true :=
  cert04_distinct_cons [18, 19] cert04_U_20 cert04_fresh_19 cert04_distinct_20
private theorem cert04_fresh_18 : !cert04_U_19.contains [19] = true := by decide +kernel
private theorem cert04_distinct_18 : distinct cert04_U_18 = true :=
  cert04_distinct_cons [19] cert04_U_19 cert04_fresh_18 cert04_distinct_19
private theorem cert04_fresh_17 : !cert04_U_18.contains [18] = true := by decide +kernel
private theorem cert04_distinct_17 : distinct cert04_U_17 = true :=
  cert04_distinct_cons [18] cert04_U_18 cert04_fresh_17 cert04_distinct_18
private theorem cert04_fresh_16 : !cert04_U_17.contains [17] = true := by decide +kernel
private theorem cert04_distinct_16 : distinct cert04_U_16 = true :=
  cert04_distinct_cons [17] cert04_U_17 cert04_fresh_16 cert04_distinct_17
private theorem cert04_fresh_15 : !cert04_U_16.contains [16] = true := by decide +kernel
private theorem cert04_distinct_15 : distinct cert04_U_15 = true :=
  cert04_distinct_cons [16] cert04_U_16 cert04_fresh_15 cert04_distinct_16
private theorem cert04_fresh_14 : !cert04_U_15.contains [15] = true := by decide +kernel
private theorem cert04_distinct_14 : distinct cert04_U_14 = true :=
  cert04_distinct_cons [15] cert04_U_15 cert04_fresh_14 cert04_distinct_15
private theorem cert04_fresh_13 : !cert04_U_14.contains [14] = true := by decide +kernel
private theorem cert04_distinct_13 : distinct cert04_U_13 = true :=
  cert04_distinct_cons [14] cert04_U_14 cert04_fresh_13 cert04_distinct_14
private theorem cert04_fresh_12 : !cert04_U_13.contains [13] = true := by decide +kernel
private theorem cert04_distinct_12 : distinct cert04_U_12 = true :=
  cert04_distinct_cons [13] cert04_U_13 cert04_fresh_12 cert04_distinct_13
private theorem cert04_fresh_11 : !cert04_U_12.contains [12] = true := by decide +kernel
private theorem cert04_distinct_11 : distinct cert04_U_11 = true :=
  cert04_distinct_cons [12] cert04_U_12 cert04_fresh_11 cert04_distinct_12
private theorem cert04_fresh_10 : !cert04_U_11.contains [11] = true := by decide +kernel
private theorem cert04_distinct_10 : distinct cert04_U_10 = true :=
  cert04_distinct_cons [11] cert04_U_11 cert04_fresh_10 cert04_distinct_11
private theorem cert04_fresh_9 : !cert04_U_10.contains [10] = true := by decide +kernel
private theorem cert04_distinct_9 : distinct cert04_U_9 = true :=
  cert04_distinct_cons [10] cert04_U_10 cert04_fresh_9 cert04_distinct_10
private theorem cert04_fresh_8 : !cert04_U_9.contains [9] = true := by decide +kernel
private theorem cert04_distinct_8 : distinct cert04_U_8 = true :=
  cert04_distinct_cons [9] cert04_U_9 cert04_fresh_8 cert04_distinct_9
private theorem cert04_fresh_7 : !cert04_U_8.contains [8] = true := by decide +kernel
private theorem cert04_distinct_7 : distinct cert04_U_7 = true :=
  cert04_distinct_cons [8] cert04_U_8 cert04_fresh_7 cert04_distinct_8
private theorem cert04_fresh_6 : !cert04_U_7.contains [7] = true := by decide +kernel
private theorem cert04_distinct_6 : distinct cert04_U_6 = true :=
  cert04_distinct_cons [7] cert04_U_7 cert04_fresh_6 cert04_distinct_7
private theorem cert04_fresh_5 : !cert04_U_6.contains [6] = true := by decide +kernel
private theorem cert04_distinct_5 : distinct cert04_U_5 = true :=
  cert04_distinct_cons [6] cert04_U_6 cert04_fresh_5 cert04_distinct_6
private theorem cert04_fresh_4 : !cert04_U_5.contains [5] = true := by decide +kernel
private theorem cert04_distinct_4 : distinct cert04_U_4 = true :=
  cert04_distinct_cons [5] cert04_U_5 cert04_fresh_4 cert04_distinct_5
private theorem cert04_fresh_3 : !cert04_U_4.contains [4] = true := by decide +kernel
private theorem cert04_distinct_3 : distinct cert04_U_3 = true :=
  cert04_distinct_cons [4] cert04_U_4 cert04_fresh_3 cert04_distinct_4
private theorem cert04_fresh_2 : !cert04_U_3.contains [3] = true := by decide +kernel
private theorem cert04_distinct_2 : distinct cert04_U_2 = true :=
  cert04_distinct_cons [3] cert04_U_3 cert04_fresh_2 cert04_distinct_3
private theorem cert04_fresh_1 : !cert04_U_2.contains [2] = true := by decide +kernel
private theorem cert04_distinct_1 : distinct cert04_U_1 = true :=
  cert04_distinct_cons [2] cert04_U_2 cert04_fresh_1 cert04_distinct_2
private theorem cert04_fresh_0 : !cert04_U_1.contains [1] = true := by decide +kernel
private theorem cert04_distinct_0 : distinct cert04_U_0 = true :=
  cert04_distinct_cons [1] cert04_U_1 cert04_fresh_0 cert04_distinct_1
private theorem cert04_closed_281 : cert04_I_281.all (fun c => (subfaces c).all cert04_I_0.contains) = true := rfl
private theorem cert04_closed_leaf_280 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 7, 18] = true := by decide +kernel
private theorem cert04_closed_280 : cert04_I_280.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 7, 18] cert04_I_281 cert04_closed_leaf_280 cert04_closed_281
private theorem cert04_closed_leaf_279 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 7, 15] = true := by decide +kernel
private theorem cert04_closed_279 : cert04_I_279.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 7, 15] cert04_I_280 cert04_closed_leaf_279 cert04_closed_280
private theorem cert04_closed_leaf_278 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 11, 19] = true := by decide +kernel
private theorem cert04_closed_278 : cert04_I_278.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 11, 19] cert04_I_279 cert04_closed_leaf_278 cert04_closed_279
private theorem cert04_closed_leaf_277 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 11, 15] = true := by decide +kernel
private theorem cert04_closed_277 : cert04_I_277.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 11, 15] cert04_I_278 cert04_closed_leaf_277 cert04_closed_278
private theorem cert04_closed_leaf_276 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 17, 19] = true := by decide +kernel
private theorem cert04_closed_276 : cert04_I_276.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 17, 19] cert04_I_277 cert04_closed_leaf_276 cert04_closed_277
private theorem cert04_closed_leaf_275 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 17, 18] = true := by decide +kernel
private theorem cert04_closed_275 : cert04_I_275.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 17, 18] cert04_I_276 cert04_closed_leaf_275 cert04_closed_276
private theorem cert04_closed_leaf_274 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 19] = true := by decide +kernel
private theorem cert04_closed_274 : cert04_I_274.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 19] cert04_I_275 cert04_closed_leaf_274 cert04_closed_275
private theorem cert04_closed_leaf_273 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 18] = true := by decide +kernel
private theorem cert04_closed_273 : cert04_I_273.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 18] cert04_I_274 cert04_closed_leaf_273 cert04_closed_274
private theorem cert04_closed_leaf_272 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 17] = true := by decide +kernel
private theorem cert04_closed_272 : cert04_I_272.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 17] cert04_I_273 cert04_closed_leaf_272 cert04_closed_273
private theorem cert04_closed_leaf_271 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 15] = true := by decide +kernel
private theorem cert04_closed_271 : cert04_I_271.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 15] cert04_I_272 cert04_closed_leaf_271 cert04_closed_272
private theorem cert04_closed_leaf_270 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 11] = true := by decide +kernel
private theorem cert04_closed_270 : cert04_I_270.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 11] cert04_I_271 cert04_closed_leaf_270 cert04_closed_271
private theorem cert04_closed_leaf_269 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 7] = true := by decide +kernel
private theorem cert04_closed_269 : cert04_I_269.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3, 7] cert04_I_270 cert04_closed_leaf_269 cert04_closed_270
private theorem cert04_closed_leaf_268 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 7, 18] = true := by decide +kernel
private theorem cert04_closed_268 : cert04_I_268.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 7, 18] cert04_I_269 cert04_closed_leaf_268 cert04_closed_269
private theorem cert04_closed_leaf_267 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 7, 15] = true := by decide +kernel
private theorem cert04_closed_267 : cert04_I_267.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 7, 15] cert04_I_268 cert04_closed_leaf_267 cert04_closed_268
private theorem cert04_closed_leaf_266 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 13, 19] = true := by decide +kernel
private theorem cert04_closed_266 : cert04_I_266.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 13, 19] cert04_I_267 cert04_closed_leaf_266 cert04_closed_267
private theorem cert04_closed_leaf_265 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 13, 15] = true := by decide +kernel
private theorem cert04_closed_265 : cert04_I_265.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 13, 15] cert04_I_266 cert04_closed_leaf_265 cert04_closed_266
private theorem cert04_closed_leaf_264 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 18, 19] = true := by decide +kernel
private theorem cert04_closed_264 : cert04_I_264.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 18, 19] cert04_I_265 cert04_closed_leaf_264 cert04_closed_265
private theorem cert04_closed_leaf_263 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 19] = true := by decide +kernel
private theorem cert04_closed_263 : cert04_I_263.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 19] cert04_I_264 cert04_closed_leaf_263 cert04_closed_264
private theorem cert04_closed_leaf_262 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 18] = true := by decide +kernel
private theorem cert04_closed_262 : cert04_I_262.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 18] cert04_I_263 cert04_closed_leaf_262 cert04_closed_263
private theorem cert04_closed_leaf_261 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 15] = true := by decide +kernel
private theorem cert04_closed_261 : cert04_I_261.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 15] cert04_I_262 cert04_closed_leaf_261 cert04_closed_262
private theorem cert04_closed_leaf_260 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 13] = true := by decide +kernel
private theorem cert04_closed_260 : cert04_I_260.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 13] cert04_I_261 cert04_closed_leaf_260 cert04_closed_261
private theorem cert04_closed_leaf_259 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 7] = true := by decide +kernel
private theorem cert04_closed_259 : cert04_I_259.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 5, 7] cert04_I_260 cert04_closed_leaf_259 cert04_closed_260
private theorem cert04_closed_leaf_258 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 7, 18] = true := by decide +kernel
private theorem cert04_closed_258 : cert04_I_258.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 7, 18] cert04_I_259 cert04_closed_leaf_258 cert04_closed_259
private theorem cert04_closed_leaf_257 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 7, 15] = true := by decide +kernel
private theorem cert04_closed_257 : cert04_I_257.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 7, 15] cert04_I_258 cert04_closed_leaf_257 cert04_closed_258
private theorem cert04_closed_leaf_256 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 11, 19] = true := by decide +kernel
private theorem cert04_closed_256 : cert04_I_256.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 11, 19] cert04_I_257 cert04_closed_leaf_256 cert04_closed_257
private theorem cert04_closed_leaf_255 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 11, 15] = true := by decide +kernel
private theorem cert04_closed_255 : cert04_I_255.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 11, 15] cert04_I_256 cert04_closed_leaf_255 cert04_closed_256
private theorem cert04_closed_leaf_254 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 13, 19] = true := by decide +kernel
private theorem cert04_closed_254 : cert04_I_254.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 13, 19] cert04_I_255 cert04_closed_leaf_254 cert04_closed_255
private theorem cert04_closed_leaf_253 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 13, 15] = true := by decide +kernel
private theorem cert04_closed_253 : cert04_I_253.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 13, 15] cert04_I_254 cert04_closed_leaf_253 cert04_closed_254
private theorem cert04_closed_leaf_252 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 19] = true := by decide +kernel
private theorem cert04_closed_252 : cert04_I_252.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 19] cert04_I_253 cert04_closed_leaf_252 cert04_closed_253
private theorem cert04_closed_leaf_251 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 15] = true := by decide +kernel
private theorem cert04_closed_251 : cert04_I_251.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 15] cert04_I_252 cert04_closed_leaf_251 cert04_closed_252
private theorem cert04_closed_leaf_250 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 13] = true := by decide +kernel
private theorem cert04_closed_250 : cert04_I_250.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 13] cert04_I_251 cert04_closed_leaf_250 cert04_closed_251
private theorem cert04_closed_leaf_249 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 11] = true := by decide +kernel
private theorem cert04_closed_249 : cert04_I_249.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 9, 11] cert04_I_250 cert04_closed_leaf_249 cert04_closed_250
private theorem cert04_closed_leaf_248 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 11, 19] = true := by decide +kernel
private theorem cert04_closed_248 : cert04_I_248.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 11, 19] cert04_I_249 cert04_closed_leaf_248 cert04_closed_249
private theorem cert04_closed_leaf_247 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 11, 15] = true := by decide +kernel
private theorem cert04_closed_247 : cert04_I_247.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 11, 15] cert04_I_248 cert04_closed_leaf_247 cert04_closed_248
private theorem cert04_closed_leaf_246 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 13, 19] = true := by decide +kernel
private theorem cert04_closed_246 : cert04_I_246.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 13, 19] cert04_I_247 cert04_closed_leaf_246 cert04_closed_247
private theorem cert04_closed_leaf_245 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 13, 15] = true := by decide +kernel
private theorem cert04_closed_245 : cert04_I_245.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 13, 15] cert04_I_246 cert04_closed_leaf_245 cert04_closed_246
private theorem cert04_closed_leaf_244 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 17, 19] = true := by decide +kernel
private theorem cert04_closed_244 : cert04_I_244.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 17, 19] cert04_I_245 cert04_closed_leaf_244 cert04_closed_245
private theorem cert04_closed_leaf_243 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 17, 18] = true := by decide +kernel
private theorem cert04_closed_243 : cert04_I_243.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 17, 18] cert04_I_244 cert04_closed_leaf_243 cert04_closed_244
private theorem cert04_closed_leaf_242 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 18, 19] = true := by decide +kernel
private theorem cert04_closed_242 : cert04_I_242.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 18, 19] cert04_I_243 cert04_closed_leaf_242 cert04_closed_243
private theorem cert04_closed_leaf_241 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 19] = true := by decide +kernel
private theorem cert04_closed_241 : cert04_I_241.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 19] cert04_I_242 cert04_closed_leaf_241 cert04_closed_242
private theorem cert04_closed_leaf_240 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 18] = true := by decide +kernel
private theorem cert04_closed_240 : cert04_I_240.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 18] cert04_I_241 cert04_closed_leaf_240 cert04_closed_241
private theorem cert04_closed_leaf_239 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 17] = true := by decide +kernel
private theorem cert04_closed_239 : cert04_I_239.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 16, 17] cert04_I_240 cert04_closed_leaf_239 cert04_closed_240
private theorem cert04_closed_leaf_238 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 17, 19] = true := by decide +kernel
private theorem cert04_closed_238 : cert04_I_238.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 17, 19] cert04_I_239 cert04_closed_leaf_238 cert04_closed_239
private theorem cert04_closed_leaf_237 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 17, 18] = true := by decide +kernel
private theorem cert04_closed_237 : cert04_I_237.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 17, 18] cert04_I_238 cert04_closed_leaf_237 cert04_closed_238
private theorem cert04_closed_leaf_236 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 18, 19] = true := by decide +kernel
private theorem cert04_closed_236 : cert04_I_236.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 18, 19] cert04_I_237 cert04_closed_leaf_236 cert04_closed_237
private theorem cert04_closed_leaf_235 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 19] = true := by decide +kernel
private theorem cert04_closed_235 : cert04_I_235.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 19] cert04_I_236 cert04_closed_leaf_235 cert04_closed_236
private theorem cert04_closed_leaf_234 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 18] = true := by decide +kernel
private theorem cert04_closed_234 : cert04_I_234.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 18] cert04_I_235 cert04_closed_leaf_234 cert04_closed_235
private theorem cert04_closed_leaf_233 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 17] = true := by decide +kernel
private theorem cert04_closed_233 : cert04_I_233.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 17] cert04_I_234 cert04_closed_leaf_233 cert04_closed_234
private theorem cert04_closed_leaf_232 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 16] = true := by decide +kernel
private theorem cert04_closed_232 : cert04_I_232.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 16] cert04_I_233 cert04_closed_leaf_232 cert04_closed_233
private theorem cert04_closed_leaf_231 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 15] = true := by decide +kernel
private theorem cert04_closed_231 : cert04_I_231.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 15] cert04_I_232 cert04_closed_leaf_231 cert04_closed_232
private theorem cert04_closed_leaf_230 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 13] = true := by decide +kernel
private theorem cert04_closed_230 : cert04_I_230.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 13] cert04_I_231 cert04_closed_leaf_230 cert04_closed_231
private theorem cert04_closed_leaf_229 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 11] = true := by decide +kernel
private theorem cert04_closed_229 : cert04_I_229.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 11] cert04_I_230 cert04_closed_leaf_229 cert04_closed_230
private theorem cert04_closed_leaf_228 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 9] = true := by decide +kernel
private theorem cert04_closed_228 : cert04_I_228.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 9] cert04_I_229 cert04_closed_leaf_228 cert04_closed_229
private theorem cert04_closed_leaf_227 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 7] = true := by decide +kernel
private theorem cert04_closed_227 : cert04_I_227.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 7] cert04_I_228 cert04_closed_leaf_227 cert04_closed_228
private theorem cert04_closed_leaf_226 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 5] = true := by decide +kernel
private theorem cert04_closed_226 : cert04_I_226.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 5] cert04_I_227 cert04_closed_leaf_226 cert04_closed_227
private theorem cert04_closed_leaf_225 : (fun c => (subfaces c).all cert04_I_0.contains) [1, 3] = true := by decide +kernel
private theorem cert04_closed_225 : cert04_I_225.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1, 3] cert04_I_226 cert04_closed_leaf_225 cert04_closed_226
private theorem cert04_closed_leaf_224 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 7, 18] = true := by decide +kernel
private theorem cert04_closed_224 : cert04_I_224.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 7, 18] cert04_I_225 cert04_closed_leaf_224 cert04_closed_225
private theorem cert04_closed_leaf_223 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 7, 15] = true := by decide +kernel
private theorem cert04_closed_223 : cert04_I_223.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 7, 15] cert04_I_224 cert04_closed_leaf_223 cert04_closed_224
private theorem cert04_closed_leaf_222 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 11, 19] = true := by decide +kernel
private theorem cert04_closed_222 : cert04_I_222.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 11, 19] cert04_I_223 cert04_closed_leaf_222 cert04_closed_223
private theorem cert04_closed_leaf_221 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 11, 15] = true := by decide +kernel
private theorem cert04_closed_221 : cert04_I_221.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 11, 15] cert04_I_222 cert04_closed_leaf_221 cert04_closed_222
private theorem cert04_closed_leaf_220 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 17, 19] = true := by decide +kernel
private theorem cert04_closed_220 : cert04_I_220.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 17, 19] cert04_I_221 cert04_closed_leaf_220 cert04_closed_221
private theorem cert04_closed_leaf_219 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 17, 18] = true := by decide +kernel
private theorem cert04_closed_219 : cert04_I_219.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 17, 18] cert04_I_220 cert04_closed_leaf_219 cert04_closed_220
private theorem cert04_closed_leaf_218 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 19] = true := by decide +kernel
private theorem cert04_closed_218 : cert04_I_218.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 19] cert04_I_219 cert04_closed_leaf_218 cert04_closed_219
private theorem cert04_closed_leaf_217 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 18] = true := by decide +kernel
private theorem cert04_closed_217 : cert04_I_217.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 18] cert04_I_218 cert04_closed_leaf_217 cert04_closed_218
private theorem cert04_closed_leaf_216 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 17] = true := by decide +kernel
private theorem cert04_closed_216 : cert04_I_216.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 17] cert04_I_217 cert04_closed_leaf_216 cert04_closed_217
private theorem cert04_closed_leaf_215 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 15] = true := by decide +kernel
private theorem cert04_closed_215 : cert04_I_215.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 15] cert04_I_216 cert04_closed_leaf_215 cert04_closed_216
private theorem cert04_closed_leaf_214 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 11] = true := by decide +kernel
private theorem cert04_closed_214 : cert04_I_214.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 11] cert04_I_215 cert04_closed_leaf_214 cert04_closed_215
private theorem cert04_closed_leaf_213 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 7] = true := by decide +kernel
private theorem cert04_closed_213 : cert04_I_213.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3, 7] cert04_I_214 cert04_closed_leaf_213 cert04_closed_214
private theorem cert04_closed_leaf_212 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 7, 18] = true := by decide +kernel
private theorem cert04_closed_212 : cert04_I_212.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 7, 18] cert04_I_213 cert04_closed_leaf_212 cert04_closed_213
private theorem cert04_closed_leaf_211 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 7, 15] = true := by decide +kernel
private theorem cert04_closed_211 : cert04_I_211.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 7, 15] cert04_I_212 cert04_closed_leaf_211 cert04_closed_212
private theorem cert04_closed_leaf_210 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 14, 19] = true := by decide +kernel
private theorem cert04_closed_210 : cert04_I_210.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 14, 19] cert04_I_211 cert04_closed_leaf_210 cert04_closed_211
private theorem cert04_closed_leaf_209 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 14, 15] = true := by decide +kernel
private theorem cert04_closed_209 : cert04_I_209.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 14, 15] cert04_I_210 cert04_closed_leaf_209 cert04_closed_210
private theorem cert04_closed_leaf_208 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 18, 19] = true := by decide +kernel
private theorem cert04_closed_208 : cert04_I_208.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 18, 19] cert04_I_209 cert04_closed_leaf_208 cert04_closed_209
private theorem cert04_closed_leaf_207 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 19] = true := by decide +kernel
private theorem cert04_closed_207 : cert04_I_207.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 19] cert04_I_208 cert04_closed_leaf_207 cert04_closed_208
private theorem cert04_closed_leaf_206 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 18] = true := by decide +kernel
private theorem cert04_closed_206 : cert04_I_206.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 18] cert04_I_207 cert04_closed_leaf_206 cert04_closed_207
private theorem cert04_closed_leaf_205 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 15] = true := by decide +kernel
private theorem cert04_closed_205 : cert04_I_205.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 15] cert04_I_206 cert04_closed_leaf_205 cert04_closed_206
private theorem cert04_closed_leaf_204 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 14] = true := by decide +kernel
private theorem cert04_closed_204 : cert04_I_204.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 14] cert04_I_205 cert04_closed_leaf_204 cert04_closed_205
private theorem cert04_closed_leaf_203 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 7] = true := by decide +kernel
private theorem cert04_closed_203 : cert04_I_203.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 6, 7] cert04_I_204 cert04_closed_leaf_203 cert04_closed_204
private theorem cert04_closed_leaf_202 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 7, 18] = true := by decide +kernel
private theorem cert04_closed_202 : cert04_I_202.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 7, 18] cert04_I_203 cert04_closed_leaf_202 cert04_closed_203
private theorem cert04_closed_leaf_201 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 7, 15] = true := by decide +kernel
private theorem cert04_closed_201 : cert04_I_201.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 7, 15] cert04_I_202 cert04_closed_leaf_201 cert04_closed_202
private theorem cert04_closed_leaf_200 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 11, 19] = true := by decide +kernel
private theorem cert04_closed_200 : cert04_I_200.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 11, 19] cert04_I_201 cert04_closed_leaf_200 cert04_closed_201
private theorem cert04_closed_leaf_199 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 11, 15] = true := by decide +kernel
private theorem cert04_closed_199 : cert04_I_199.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 11, 15] cert04_I_200 cert04_closed_leaf_199 cert04_closed_200
private theorem cert04_closed_leaf_198 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 14, 19] = true := by decide +kernel
private theorem cert04_closed_198 : cert04_I_198.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 14, 19] cert04_I_199 cert04_closed_leaf_198 cert04_closed_199
private theorem cert04_closed_leaf_197 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 14, 15] = true := by decide +kernel
private theorem cert04_closed_197 : cert04_I_197.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 14, 15] cert04_I_198 cert04_closed_leaf_197 cert04_closed_198
private theorem cert04_closed_leaf_196 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 19] = true := by decide +kernel
private theorem cert04_closed_196 : cert04_I_196.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 19] cert04_I_197 cert04_closed_leaf_196 cert04_closed_197
private theorem cert04_closed_leaf_195 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 15] = true := by decide +kernel
private theorem cert04_closed_195 : cert04_I_195.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 15] cert04_I_196 cert04_closed_leaf_195 cert04_closed_196
private theorem cert04_closed_leaf_194 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 14] = true := by decide +kernel
private theorem cert04_closed_194 : cert04_I_194.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 14] cert04_I_195 cert04_closed_leaf_194 cert04_closed_195
private theorem cert04_closed_leaf_193 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 11] = true := by decide +kernel
private theorem cert04_closed_193 : cert04_I_193.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 10, 11] cert04_I_194 cert04_closed_leaf_193 cert04_closed_194
private theorem cert04_closed_leaf_192 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 11, 19] = true := by decide +kernel
private theorem cert04_closed_192 : cert04_I_192.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 11, 19] cert04_I_193 cert04_closed_leaf_192 cert04_closed_193
private theorem cert04_closed_leaf_191 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 11, 15] = true := by decide +kernel
private theorem cert04_closed_191 : cert04_I_191.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 11, 15] cert04_I_192 cert04_closed_leaf_191 cert04_closed_192
private theorem cert04_closed_leaf_190 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 14, 19] = true := by decide +kernel
private theorem cert04_closed_190 : cert04_I_190.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 14, 19] cert04_I_191 cert04_closed_leaf_190 cert04_closed_191
private theorem cert04_closed_leaf_189 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 14, 15] = true := by decide +kernel
private theorem cert04_closed_189 : cert04_I_189.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 14, 15] cert04_I_190 cert04_closed_leaf_189 cert04_closed_190
private theorem cert04_closed_leaf_188 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 17, 18, 19] = true := by decide +kernel
private theorem cert04_closed_188 : cert04_I_188.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 17, 18, 19] cert04_I_189 cert04_closed_leaf_188 cert04_closed_189
private theorem cert04_closed_leaf_187 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 17, 19] = true := by decide +kernel
private theorem cert04_closed_187 : cert04_I_187.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 17, 19] cert04_I_188 cert04_closed_leaf_187 cert04_closed_188
private theorem cert04_closed_leaf_186 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 17, 18] = true := by decide +kernel
private theorem cert04_closed_186 : cert04_I_186.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 17, 18] cert04_I_187 cert04_closed_leaf_186 cert04_closed_187
private theorem cert04_closed_leaf_185 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 18, 19] = true := by decide +kernel
private theorem cert04_closed_185 : cert04_I_185.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 18, 19] cert04_I_186 cert04_closed_leaf_185 cert04_closed_186
private theorem cert04_closed_leaf_184 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 19] = true := by decide +kernel
private theorem cert04_closed_184 : cert04_I_184.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 19] cert04_I_185 cert04_closed_leaf_184 cert04_closed_185
private theorem cert04_closed_leaf_183 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 18] = true := by decide +kernel
private theorem cert04_closed_183 : cert04_I_183.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 18] cert04_I_184 cert04_closed_leaf_183 cert04_closed_184
private theorem cert04_closed_leaf_182 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 17] = true := by decide +kernel
private theorem cert04_closed_182 : cert04_I_182.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 17] cert04_I_183 cert04_closed_leaf_182 cert04_closed_183
private theorem cert04_closed_leaf_181 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 15] = true := by decide +kernel
private theorem cert04_closed_181 : cert04_I_181.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 15] cert04_I_182 cert04_closed_leaf_181 cert04_closed_182
private theorem cert04_closed_leaf_180 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 14] = true := by decide +kernel
private theorem cert04_closed_180 : cert04_I_180.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 14] cert04_I_181 cert04_closed_leaf_180 cert04_closed_181
private theorem cert04_closed_leaf_179 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 11] = true := by decide +kernel
private theorem cert04_closed_179 : cert04_I_179.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 11] cert04_I_180 cert04_closed_leaf_179 cert04_closed_180
private theorem cert04_closed_leaf_178 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 10] = true := by decide +kernel
private theorem cert04_closed_178 : cert04_I_178.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 10] cert04_I_179 cert04_closed_leaf_178 cert04_closed_179
private theorem cert04_closed_leaf_177 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 7] = true := by decide +kernel
private theorem cert04_closed_177 : cert04_I_177.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 7] cert04_I_178 cert04_closed_leaf_177 cert04_closed_178
private theorem cert04_closed_leaf_176 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 6] = true := by decide +kernel
private theorem cert04_closed_176 : cert04_I_176.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 6] cert04_I_177 cert04_closed_leaf_176 cert04_closed_177
private theorem cert04_closed_leaf_175 : (fun c => (subfaces c).all cert04_I_0.contains) [2, 3] = true := by decide +kernel
private theorem cert04_closed_175 : cert04_I_175.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2, 3] cert04_I_176 cert04_closed_leaf_175 cert04_closed_176
private theorem cert04_closed_leaf_174 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 7, 18] = true := by decide +kernel
private theorem cert04_closed_174 : cert04_I_174.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 7, 18] cert04_I_175 cert04_closed_leaf_174 cert04_closed_175
private theorem cert04_closed_leaf_173 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 7, 15] = true := by decide +kernel
private theorem cert04_closed_173 : cert04_I_173.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 7, 15] cert04_I_174 cert04_closed_leaf_173 cert04_closed_174
private theorem cert04_closed_leaf_172 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 11, 19] = true := by decide +kernel
private theorem cert04_closed_172 : cert04_I_172.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 11, 19] cert04_I_173 cert04_closed_leaf_172 cert04_closed_173
private theorem cert04_closed_leaf_171 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 11, 15] = true := by decide +kernel
private theorem cert04_closed_171 : cert04_I_171.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 11, 15] cert04_I_172 cert04_closed_leaf_171 cert04_closed_172
private theorem cert04_closed_leaf_170 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 17, 19] = true := by decide +kernel
private theorem cert04_closed_170 : cert04_I_170.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 17, 19] cert04_I_171 cert04_closed_leaf_170 cert04_closed_171
private theorem cert04_closed_leaf_169 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 17, 18] = true := by decide +kernel
private theorem cert04_closed_169 : cert04_I_169.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 17, 18] cert04_I_170 cert04_closed_leaf_169 cert04_closed_170
private theorem cert04_closed_leaf_168 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 19] = true := by decide +kernel
private theorem cert04_closed_168 : cert04_I_168.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 19] cert04_I_169 cert04_closed_leaf_168 cert04_closed_169
private theorem cert04_closed_leaf_167 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 18] = true := by decide +kernel
private theorem cert04_closed_167 : cert04_I_167.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 18] cert04_I_168 cert04_closed_leaf_167 cert04_closed_168
private theorem cert04_closed_leaf_166 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 17] = true := by decide +kernel
private theorem cert04_closed_166 : cert04_I_166.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 17] cert04_I_167 cert04_closed_leaf_166 cert04_closed_167
private theorem cert04_closed_leaf_165 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 15] = true := by decide +kernel
private theorem cert04_closed_165 : cert04_I_165.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 15] cert04_I_166 cert04_closed_leaf_165 cert04_closed_166
private theorem cert04_closed_leaf_164 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 11] = true := by decide +kernel
private theorem cert04_closed_164 : cert04_I_164.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 11] cert04_I_165 cert04_closed_leaf_164 cert04_closed_165
private theorem cert04_closed_leaf_163 : (fun c => (subfaces c).all cert04_I_0.contains) [3, 7] = true := by decide +kernel
private theorem cert04_closed_163 : cert04_I_163.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3, 7] cert04_I_164 cert04_closed_leaf_163 cert04_closed_164
private theorem cert04_closed_leaf_162 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 7, 18] = true := by decide +kernel
private theorem cert04_closed_162 : cert04_I_162.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 7, 18] cert04_I_163 cert04_closed_leaf_162 cert04_closed_163
private theorem cert04_closed_leaf_161 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 7, 15] = true := by decide +kernel
private theorem cert04_closed_161 : cert04_I_161.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 7, 15] cert04_I_162 cert04_closed_leaf_161 cert04_closed_162
private theorem cert04_closed_leaf_160 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 13, 19] = true := by decide +kernel
private theorem cert04_closed_160 : cert04_I_160.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 13, 19] cert04_I_161 cert04_closed_leaf_160 cert04_closed_161
private theorem cert04_closed_leaf_159 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 13, 15] = true := by decide +kernel
private theorem cert04_closed_159 : cert04_I_159.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 13, 15] cert04_I_160 cert04_closed_leaf_159 cert04_closed_160
private theorem cert04_closed_leaf_158 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 18, 19] = true := by decide +kernel
private theorem cert04_closed_158 : cert04_I_158.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 18, 19] cert04_I_159 cert04_closed_leaf_158 cert04_closed_159
private theorem cert04_closed_leaf_157 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 19] = true := by decide +kernel
private theorem cert04_closed_157 : cert04_I_157.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 19] cert04_I_158 cert04_closed_leaf_157 cert04_closed_158
private theorem cert04_closed_leaf_156 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 18] = true := by decide +kernel
private theorem cert04_closed_156 : cert04_I_156.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 18] cert04_I_157 cert04_closed_leaf_156 cert04_closed_157
private theorem cert04_closed_leaf_155 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 15] = true := by decide +kernel
private theorem cert04_closed_155 : cert04_I_155.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 15] cert04_I_156 cert04_closed_leaf_155 cert04_closed_156
private theorem cert04_closed_leaf_154 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 13] = true := by decide +kernel
private theorem cert04_closed_154 : cert04_I_154.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 13] cert04_I_155 cert04_closed_leaf_154 cert04_closed_155
private theorem cert04_closed_leaf_153 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 7] = true := by decide +kernel
private theorem cert04_closed_153 : cert04_I_153.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 5, 7] cert04_I_154 cert04_closed_leaf_153 cert04_closed_154
private theorem cert04_closed_leaf_152 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 7, 18] = true := by decide +kernel
private theorem cert04_closed_152 : cert04_I_152.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 7, 18] cert04_I_153 cert04_closed_leaf_152 cert04_closed_153
private theorem cert04_closed_leaf_151 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 7, 15] = true := by decide +kernel
private theorem cert04_closed_151 : cert04_I_151.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 7, 15] cert04_I_152 cert04_closed_leaf_151 cert04_closed_152
private theorem cert04_closed_leaf_150 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 14, 19] = true := by decide +kernel
private theorem cert04_closed_150 : cert04_I_150.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 14, 19] cert04_I_151 cert04_closed_leaf_150 cert04_closed_151
private theorem cert04_closed_leaf_149 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 14, 15] = true := by decide +kernel
private theorem cert04_closed_149 : cert04_I_149.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 14, 15] cert04_I_150 cert04_closed_leaf_149 cert04_closed_150
private theorem cert04_closed_leaf_148 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 18, 19] = true := by decide +kernel
private theorem cert04_closed_148 : cert04_I_148.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 18, 19] cert04_I_149 cert04_closed_leaf_148 cert04_closed_149
private theorem cert04_closed_leaf_147 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 19] = true := by decide +kernel
private theorem cert04_closed_147 : cert04_I_147.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 19] cert04_I_148 cert04_closed_leaf_147 cert04_closed_148
private theorem cert04_closed_leaf_146 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 18] = true := by decide +kernel
private theorem cert04_closed_146 : cert04_I_146.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 18] cert04_I_147 cert04_closed_leaf_146 cert04_closed_147
private theorem cert04_closed_leaf_145 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 15] = true := by decide +kernel
private theorem cert04_closed_145 : cert04_I_145.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 15] cert04_I_146 cert04_closed_leaf_145 cert04_closed_146
private theorem cert04_closed_leaf_144 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 14] = true := by decide +kernel
private theorem cert04_closed_144 : cert04_I_144.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 14] cert04_I_145 cert04_closed_leaf_144 cert04_closed_145
private theorem cert04_closed_leaf_143 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 7] = true := by decide +kernel
private theorem cert04_closed_143 : cert04_I_143.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 6, 7] cert04_I_144 cert04_closed_leaf_143 cert04_closed_144
private theorem cert04_closed_leaf_142 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 7, 18] = true := by decide +kernel
private theorem cert04_closed_142 : cert04_I_142.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 7, 18] cert04_I_143 cert04_closed_leaf_142 cert04_closed_143
private theorem cert04_closed_leaf_141 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 7, 15] = true := by decide +kernel
private theorem cert04_closed_141 : cert04_I_141.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 7, 15] cert04_I_142 cert04_closed_leaf_141 cert04_closed_142
private theorem cert04_closed_leaf_140 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 13, 19] = true := by decide +kernel
private theorem cert04_closed_140 : cert04_I_140.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 13, 19] cert04_I_141 cert04_closed_leaf_140 cert04_closed_141
private theorem cert04_closed_leaf_139 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 13, 15] = true := by decide +kernel
private theorem cert04_closed_139 : cert04_I_139.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 13, 15] cert04_I_140 cert04_closed_leaf_139 cert04_closed_140
private theorem cert04_closed_leaf_138 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 14, 19] = true := by decide +kernel
private theorem cert04_closed_138 : cert04_I_138.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 14, 19] cert04_I_139 cert04_closed_leaf_138 cert04_closed_139
private theorem cert04_closed_leaf_137 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 14, 15] = true := by decide +kernel
private theorem cert04_closed_137 : cert04_I_137.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 14, 15] cert04_I_138 cert04_closed_leaf_137 cert04_closed_138
private theorem cert04_closed_leaf_136 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 19] = true := by decide +kernel
private theorem cert04_closed_136 : cert04_I_136.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 19] cert04_I_137 cert04_closed_leaf_136 cert04_closed_137
private theorem cert04_closed_leaf_135 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 15] = true := by decide +kernel
private theorem cert04_closed_135 : cert04_I_135.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 15] cert04_I_136 cert04_closed_leaf_135 cert04_closed_136
private theorem cert04_closed_leaf_134 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 14] = true := by decide +kernel
private theorem cert04_closed_134 : cert04_I_134.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 14] cert04_I_135 cert04_closed_leaf_134 cert04_closed_135
private theorem cert04_closed_leaf_133 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 13] = true := by decide +kernel
private theorem cert04_closed_133 : cert04_I_133.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 12, 13] cert04_I_134 cert04_closed_leaf_133 cert04_closed_134
private theorem cert04_closed_leaf_132 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 13, 19] = true := by decide +kernel
private theorem cert04_closed_132 : cert04_I_132.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 13, 19] cert04_I_133 cert04_closed_leaf_132 cert04_closed_133
private theorem cert04_closed_leaf_131 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 13, 15] = true := by decide +kernel
private theorem cert04_closed_131 : cert04_I_131.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 13, 15] cert04_I_132 cert04_closed_leaf_131 cert04_closed_132
private theorem cert04_closed_leaf_130 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 14, 19] = true := by decide +kernel
private theorem cert04_closed_130 : cert04_I_130.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 14, 19] cert04_I_131 cert04_closed_leaf_130 cert04_closed_131
private theorem cert04_closed_leaf_129 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 14, 15] = true := by decide +kernel
private theorem cert04_closed_129 : cert04_I_129.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 14, 15] cert04_I_130 cert04_closed_leaf_129 cert04_closed_130
private theorem cert04_closed_leaf_128 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 18, 19] = true := by decide +kernel
private theorem cert04_closed_128 : cert04_I_128.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 18, 19] cert04_I_129 cert04_closed_leaf_128 cert04_closed_129
private theorem cert04_closed_leaf_127 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 19] = true := by decide +kernel
private theorem cert04_closed_127 : cert04_I_127.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 19] cert04_I_128 cert04_closed_leaf_127 cert04_closed_128
private theorem cert04_closed_leaf_126 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 18] = true := by decide +kernel
private theorem cert04_closed_126 : cert04_I_126.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 18] cert04_I_127 cert04_closed_leaf_126 cert04_closed_127
private theorem cert04_closed_leaf_125 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 15] = true := by decide +kernel
private theorem cert04_closed_125 : cert04_I_125.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 15] cert04_I_126 cert04_closed_leaf_125 cert04_closed_126
private theorem cert04_closed_leaf_124 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 14] = true := by decide +kernel
private theorem cert04_closed_124 : cert04_I_124.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 14] cert04_I_125 cert04_closed_leaf_124 cert04_closed_125
private theorem cert04_closed_leaf_123 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 13] = true := by decide +kernel
private theorem cert04_closed_123 : cert04_I_123.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 13] cert04_I_124 cert04_closed_leaf_123 cert04_closed_124
private theorem cert04_closed_leaf_122 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 12] = true := by decide +kernel
private theorem cert04_closed_122 : cert04_I_122.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 12] cert04_I_123 cert04_closed_leaf_122 cert04_closed_123
private theorem cert04_closed_leaf_121 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 7] = true := by decide +kernel
private theorem cert04_closed_121 : cert04_I_121.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 7] cert04_I_122 cert04_closed_leaf_121 cert04_closed_122
private theorem cert04_closed_leaf_120 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 6] = true := by decide +kernel
private theorem cert04_closed_120 : cert04_I_120.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 6] cert04_I_121 cert04_closed_leaf_120 cert04_closed_121
private theorem cert04_closed_leaf_119 : (fun c => (subfaces c).all cert04_I_0.contains) [4, 5] = true := by decide +kernel
private theorem cert04_closed_119 : cert04_I_119.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4, 5] cert04_I_120 cert04_closed_leaf_119 cert04_closed_120
private theorem cert04_closed_leaf_118 : (fun c => (subfaces c).all cert04_I_0.contains) [5, 7, 18] = true := by decide +kernel
private theorem cert04_closed_118 : cert04_I_118.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [5, 7, 18] cert04_I_119 cert04_closed_leaf_118 cert04_closed_119
private theorem cert04_closed_leaf_117 : (fun c => (subfaces c).all cert04_I_0.contains) [5, 7, 15] = true := by decide +kernel
private theorem cert04_closed_117 : cert04_I_117.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [5, 7, 15] cert04_I_118 cert04_closed_leaf_117 cert04_closed_118
private theorem cert04_closed_leaf_116 : (fun c => (subfaces c).all cert04_I_0.contains) [5, 13, 19] = true := by decide +kernel
private theorem cert04_closed_116 : cert04_I_116.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [5, 13, 19] cert04_I_117 cert04_closed_leaf_116 cert04_closed_117
private theorem cert04_closed_leaf_115 : (fun c => (subfaces c).all cert04_I_0.contains) [5, 13, 15] = true := by decide +kernel
private theorem cert04_closed_115 : cert04_I_115.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [5, 13, 15] cert04_I_116 cert04_closed_leaf_115 cert04_closed_116
private theorem cert04_closed_leaf_114 : (fun c => (subfaces c).all cert04_I_0.contains) [5, 18, 19] = true := by decide +kernel
private theorem cert04_closed_114 : cert04_I_114.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [5, 18, 19] cert04_I_115 cert04_closed_leaf_114 cert04_closed_115
private theorem cert04_closed_leaf_113 : (fun c => (subfaces c).all cert04_I_0.contains) [5, 19] = true := by decide +kernel
private theorem cert04_closed_113 : cert04_I_113.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [5, 19] cert04_I_114 cert04_closed_leaf_113 cert04_closed_114
private theorem cert04_closed_leaf_112 : (fun c => (subfaces c).all cert04_I_0.contains) [5, 18] = true := by decide +kernel
private theorem cert04_closed_112 : cert04_I_112.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [5, 18] cert04_I_113 cert04_closed_leaf_112 cert04_closed_113
private theorem cert04_closed_leaf_111 : (fun c => (subfaces c).all cert04_I_0.contains) [5, 15] = true := by decide +kernel
private theorem cert04_closed_111 : cert04_I_111.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [5, 15] cert04_I_112 cert04_closed_leaf_111 cert04_closed_112
private theorem cert04_closed_leaf_110 : (fun c => (subfaces c).all cert04_I_0.contains) [5, 13] = true := by decide +kernel
private theorem cert04_closed_110 : cert04_I_110.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [5, 13] cert04_I_111 cert04_closed_leaf_110 cert04_closed_111
private theorem cert04_closed_leaf_109 : (fun c => (subfaces c).all cert04_I_0.contains) [5, 7] = true := by decide +kernel
private theorem cert04_closed_109 : cert04_I_109.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [5, 7] cert04_I_110 cert04_closed_leaf_109 cert04_closed_110
private theorem cert04_closed_leaf_108 : (fun c => (subfaces c).all cert04_I_0.contains) [6, 7, 18] = true := by decide +kernel
private theorem cert04_closed_108 : cert04_I_108.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [6, 7, 18] cert04_I_109 cert04_closed_leaf_108 cert04_closed_109
private theorem cert04_closed_leaf_107 : (fun c => (subfaces c).all cert04_I_0.contains) [6, 7, 15] = true := by decide +kernel
private theorem cert04_closed_107 : cert04_I_107.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [6, 7, 15] cert04_I_108 cert04_closed_leaf_107 cert04_closed_108
private theorem cert04_closed_leaf_106 : (fun c => (subfaces c).all cert04_I_0.contains) [6, 14, 19] = true := by decide +kernel
private theorem cert04_closed_106 : cert04_I_106.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [6, 14, 19] cert04_I_107 cert04_closed_leaf_106 cert04_closed_107
private theorem cert04_closed_leaf_105 : (fun c => (subfaces c).all cert04_I_0.contains) [6, 14, 15] = true := by decide +kernel
private theorem cert04_closed_105 : cert04_I_105.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [6, 14, 15] cert04_I_106 cert04_closed_leaf_105 cert04_closed_106
private theorem cert04_closed_leaf_104 : (fun c => (subfaces c).all cert04_I_0.contains) [6, 18, 19] = true := by decide +kernel
private theorem cert04_closed_104 : cert04_I_104.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [6, 18, 19] cert04_I_105 cert04_closed_leaf_104 cert04_closed_105
private theorem cert04_closed_leaf_103 : (fun c => (subfaces c).all cert04_I_0.contains) [6, 19] = true := by decide +kernel
private theorem cert04_closed_103 : cert04_I_103.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [6, 19] cert04_I_104 cert04_closed_leaf_103 cert04_closed_104
private theorem cert04_closed_leaf_102 : (fun c => (subfaces c).all cert04_I_0.contains) [6, 18] = true := by decide +kernel
private theorem cert04_closed_102 : cert04_I_102.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [6, 18] cert04_I_103 cert04_closed_leaf_102 cert04_closed_103
private theorem cert04_closed_leaf_101 : (fun c => (subfaces c).all cert04_I_0.contains) [6, 15] = true := by decide +kernel
private theorem cert04_closed_101 : cert04_I_101.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [6, 15] cert04_I_102 cert04_closed_leaf_101 cert04_closed_102
private theorem cert04_closed_leaf_100 : (fun c => (subfaces c).all cert04_I_0.contains) [6, 14] = true := by decide +kernel
private theorem cert04_closed_100 : cert04_I_100.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [6, 14] cert04_I_101 cert04_closed_leaf_100 cert04_closed_101
private theorem cert04_closed_leaf_99 : (fun c => (subfaces c).all cert04_I_0.contains) [6, 7] = true := by decide +kernel
private theorem cert04_closed_99 : cert04_I_99.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [6, 7] cert04_I_100 cert04_closed_leaf_99 cert04_closed_100
private theorem cert04_closed_leaf_98 : (fun c => (subfaces c).all cert04_I_0.contains) [7, 18] = true := by decide +kernel
private theorem cert04_closed_98 : cert04_I_98.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [7, 18] cert04_I_99 cert04_closed_leaf_98 cert04_closed_99
private theorem cert04_closed_leaf_97 : (fun c => (subfaces c).all cert04_I_0.contains) [7, 15] = true := by decide +kernel
private theorem cert04_closed_97 : cert04_I_97.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [7, 15] cert04_I_98 cert04_closed_leaf_97 cert04_closed_98
private theorem cert04_closed_leaf_96 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 11, 19] = true := by decide +kernel
private theorem cert04_closed_96 : cert04_I_96.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 11, 19] cert04_I_97 cert04_closed_leaf_96 cert04_closed_97
private theorem cert04_closed_leaf_95 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 11, 15] = true := by decide +kernel
private theorem cert04_closed_95 : cert04_I_95.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 11, 15] cert04_I_96 cert04_closed_leaf_95 cert04_closed_96
private theorem cert04_closed_leaf_94 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 13, 19] = true := by decide +kernel
private theorem cert04_closed_94 : cert04_I_94.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 13, 19] cert04_I_95 cert04_closed_leaf_94 cert04_closed_95
private theorem cert04_closed_leaf_93 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 13, 15] = true := by decide +kernel
private theorem cert04_closed_93 : cert04_I_93.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 13, 15] cert04_I_94 cert04_closed_leaf_93 cert04_closed_94
private theorem cert04_closed_leaf_92 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 19] = true := by decide +kernel
private theorem cert04_closed_92 : cert04_I_92.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 19] cert04_I_93 cert04_closed_leaf_92 cert04_closed_93
private theorem cert04_closed_leaf_91 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 15] = true := by decide +kernel
private theorem cert04_closed_91 : cert04_I_91.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 15] cert04_I_92 cert04_closed_leaf_91 cert04_closed_92
private theorem cert04_closed_leaf_90 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 13] = true := by decide +kernel
private theorem cert04_closed_90 : cert04_I_90.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 13] cert04_I_91 cert04_closed_leaf_90 cert04_closed_91
private theorem cert04_closed_leaf_89 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 11] = true := by decide +kernel
private theorem cert04_closed_89 : cert04_I_89.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 9, 11] cert04_I_90 cert04_closed_leaf_89 cert04_closed_90
private theorem cert04_closed_leaf_88 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 11, 19] = true := by decide +kernel
private theorem cert04_closed_88 : cert04_I_88.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 11, 19] cert04_I_89 cert04_closed_leaf_88 cert04_closed_89
private theorem cert04_closed_leaf_87 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 11, 15] = true := by decide +kernel
private theorem cert04_closed_87 : cert04_I_87.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 11, 15] cert04_I_88 cert04_closed_leaf_87 cert04_closed_88
private theorem cert04_closed_leaf_86 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 14, 19] = true := by decide +kernel
private theorem cert04_closed_86 : cert04_I_86.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 14, 19] cert04_I_87 cert04_closed_leaf_86 cert04_closed_87
private theorem cert04_closed_leaf_85 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 14, 15] = true := by decide +kernel
private theorem cert04_closed_85 : cert04_I_85.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 14, 15] cert04_I_86 cert04_closed_leaf_85 cert04_closed_86
private theorem cert04_closed_leaf_84 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 19] = true := by decide +kernel
private theorem cert04_closed_84 : cert04_I_84.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 19] cert04_I_85 cert04_closed_leaf_84 cert04_closed_85
private theorem cert04_closed_leaf_83 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 15] = true := by decide +kernel
private theorem cert04_closed_83 : cert04_I_83.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 15] cert04_I_84 cert04_closed_leaf_83 cert04_closed_84
private theorem cert04_closed_leaf_82 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 14] = true := by decide +kernel
private theorem cert04_closed_82 : cert04_I_82.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 14] cert04_I_83 cert04_closed_leaf_82 cert04_closed_83
private theorem cert04_closed_leaf_81 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 11] = true := by decide +kernel
private theorem cert04_closed_81 : cert04_I_81.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 10, 11] cert04_I_82 cert04_closed_leaf_81 cert04_closed_82
private theorem cert04_closed_leaf_80 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 11, 19] = true := by decide +kernel
private theorem cert04_closed_80 : cert04_I_80.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 11, 19] cert04_I_81 cert04_closed_leaf_80 cert04_closed_81
private theorem cert04_closed_leaf_79 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 11, 15] = true := by decide +kernel
private theorem cert04_closed_79 : cert04_I_79.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 11, 15] cert04_I_80 cert04_closed_leaf_79 cert04_closed_80
private theorem cert04_closed_leaf_78 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 13, 19] = true := by decide +kernel
private theorem cert04_closed_78 : cert04_I_78.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 13, 19] cert04_I_79 cert04_closed_leaf_78 cert04_closed_79
private theorem cert04_closed_leaf_77 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 13, 15] = true := by decide +kernel
private theorem cert04_closed_77 : cert04_I_77.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 13, 15] cert04_I_78 cert04_closed_leaf_77 cert04_closed_78
private theorem cert04_closed_leaf_76 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 14, 19] = true := by decide +kernel
private theorem cert04_closed_76 : cert04_I_76.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 14, 19] cert04_I_77 cert04_closed_leaf_76 cert04_closed_77
private theorem cert04_closed_leaf_75 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 14, 15] = true := by decide +kernel
private theorem cert04_closed_75 : cert04_I_75.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 14, 15] cert04_I_76 cert04_closed_leaf_75 cert04_closed_76
private theorem cert04_closed_leaf_74 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 19] = true := by decide +kernel
private theorem cert04_closed_74 : cert04_I_74.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 19] cert04_I_75 cert04_closed_leaf_74 cert04_closed_75
private theorem cert04_closed_leaf_73 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 15] = true := by decide +kernel
private theorem cert04_closed_73 : cert04_I_73.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 15] cert04_I_74 cert04_closed_leaf_73 cert04_closed_74
private theorem cert04_closed_leaf_72 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 14] = true := by decide +kernel
private theorem cert04_closed_72 : cert04_I_72.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 14] cert04_I_73 cert04_closed_leaf_72 cert04_closed_73
private theorem cert04_closed_leaf_71 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 13] = true := by decide +kernel
private theorem cert04_closed_71 : cert04_I_71.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 12, 13] cert04_I_72 cert04_closed_leaf_71 cert04_closed_72
private theorem cert04_closed_leaf_70 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 13, 19] = true := by decide +kernel
private theorem cert04_closed_70 : cert04_I_70.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 13, 19] cert04_I_71 cert04_closed_leaf_70 cert04_closed_71
private theorem cert04_closed_leaf_69 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 13, 15] = true := by decide +kernel
private theorem cert04_closed_69 : cert04_I_69.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 13, 15] cert04_I_70 cert04_closed_leaf_69 cert04_closed_70
private theorem cert04_closed_leaf_68 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 14, 19] = true := by decide +kernel
private theorem cert04_closed_68 : cert04_I_68.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 14, 19] cert04_I_69 cert04_closed_leaf_68 cert04_closed_69
private theorem cert04_closed_leaf_67 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 14, 15] = true := by decide +kernel
private theorem cert04_closed_67 : cert04_I_67.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 14, 15] cert04_I_68 cert04_closed_leaf_67 cert04_closed_68
private theorem cert04_closed_leaf_66 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 19] = true := by decide +kernel
private theorem cert04_closed_66 : cert04_I_66.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 19] cert04_I_67 cert04_closed_leaf_66 cert04_closed_67
private theorem cert04_closed_leaf_65 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 15] = true := by decide +kernel
private theorem cert04_closed_65 : cert04_I_65.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 15] cert04_I_66 cert04_closed_leaf_65 cert04_closed_66
private theorem cert04_closed_leaf_64 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 14] = true := by decide +kernel
private theorem cert04_closed_64 : cert04_I_64.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 14] cert04_I_65 cert04_closed_leaf_64 cert04_closed_65
private theorem cert04_closed_leaf_63 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 13] = true := by decide +kernel
private theorem cert04_closed_63 : cert04_I_63.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 13] cert04_I_64 cert04_closed_leaf_63 cert04_closed_64
private theorem cert04_closed_leaf_62 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 12] = true := by decide +kernel
private theorem cert04_closed_62 : cert04_I_62.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 12] cert04_I_63 cert04_closed_leaf_62 cert04_closed_63
private theorem cert04_closed_leaf_61 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 11] = true := by decide +kernel
private theorem cert04_closed_61 : cert04_I_61.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 11] cert04_I_62 cert04_closed_leaf_61 cert04_closed_62
private theorem cert04_closed_leaf_60 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 10] = true := by decide +kernel
private theorem cert04_closed_60 : cert04_I_60.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 10] cert04_I_61 cert04_closed_leaf_60 cert04_closed_61
private theorem cert04_closed_leaf_59 : (fun c => (subfaces c).all cert04_I_0.contains) [8, 9] = true := by decide +kernel
private theorem cert04_closed_59 : cert04_I_59.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8, 9] cert04_I_60 cert04_closed_leaf_59 cert04_closed_60
private theorem cert04_closed_leaf_58 : (fun c => (subfaces c).all cert04_I_0.contains) [9, 11, 19] = true := by decide +kernel
private theorem cert04_closed_58 : cert04_I_58.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [9, 11, 19] cert04_I_59 cert04_closed_leaf_58 cert04_closed_59
private theorem cert04_closed_leaf_57 : (fun c => (subfaces c).all cert04_I_0.contains) [9, 11, 15] = true := by decide +kernel
private theorem cert04_closed_57 : cert04_I_57.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [9, 11, 15] cert04_I_58 cert04_closed_leaf_57 cert04_closed_58
private theorem cert04_closed_leaf_56 : (fun c => (subfaces c).all cert04_I_0.contains) [9, 13, 19] = true := by decide +kernel
private theorem cert04_closed_56 : cert04_I_56.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [9, 13, 19] cert04_I_57 cert04_closed_leaf_56 cert04_closed_57
private theorem cert04_closed_leaf_55 : (fun c => (subfaces c).all cert04_I_0.contains) [9, 13, 15] = true := by decide +kernel
private theorem cert04_closed_55 : cert04_I_55.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [9, 13, 15] cert04_I_56 cert04_closed_leaf_55 cert04_closed_56
private theorem cert04_closed_leaf_54 : (fun c => (subfaces c).all cert04_I_0.contains) [9, 19] = true := by decide +kernel
private theorem cert04_closed_54 : cert04_I_54.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [9, 19] cert04_I_55 cert04_closed_leaf_54 cert04_closed_55
private theorem cert04_closed_leaf_53 : (fun c => (subfaces c).all cert04_I_0.contains) [9, 15] = true := by decide +kernel
private theorem cert04_closed_53 : cert04_I_53.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [9, 15] cert04_I_54 cert04_closed_leaf_53 cert04_closed_54
private theorem cert04_closed_leaf_52 : (fun c => (subfaces c).all cert04_I_0.contains) [9, 13] = true := by decide +kernel
private theorem cert04_closed_52 : cert04_I_52.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [9, 13] cert04_I_53 cert04_closed_leaf_52 cert04_closed_53
private theorem cert04_closed_leaf_51 : (fun c => (subfaces c).all cert04_I_0.contains) [9, 11] = true := by decide +kernel
private theorem cert04_closed_51 : cert04_I_51.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [9, 11] cert04_I_52 cert04_closed_leaf_51 cert04_closed_52
private theorem cert04_closed_leaf_50 : (fun c => (subfaces c).all cert04_I_0.contains) [10, 11, 19] = true := by decide +kernel
private theorem cert04_closed_50 : cert04_I_50.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [10, 11, 19] cert04_I_51 cert04_closed_leaf_50 cert04_closed_51
private theorem cert04_closed_leaf_49 : (fun c => (subfaces c).all cert04_I_0.contains) [10, 11, 15] = true := by decide +kernel
private theorem cert04_closed_49 : cert04_I_49.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [10, 11, 15] cert04_I_50 cert04_closed_leaf_49 cert04_closed_50
private theorem cert04_closed_leaf_48 : (fun c => (subfaces c).all cert04_I_0.contains) [10, 14, 19] = true := by decide +kernel
private theorem cert04_closed_48 : cert04_I_48.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [10, 14, 19] cert04_I_49 cert04_closed_leaf_48 cert04_closed_49
private theorem cert04_closed_leaf_47 : (fun c => (subfaces c).all cert04_I_0.contains) [10, 14, 15] = true := by decide +kernel
private theorem cert04_closed_47 : cert04_I_47.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [10, 14, 15] cert04_I_48 cert04_closed_leaf_47 cert04_closed_48
private theorem cert04_closed_leaf_46 : (fun c => (subfaces c).all cert04_I_0.contains) [10, 19] = true := by decide +kernel
private theorem cert04_closed_46 : cert04_I_46.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [10, 19] cert04_I_47 cert04_closed_leaf_46 cert04_closed_47
private theorem cert04_closed_leaf_45 : (fun c => (subfaces c).all cert04_I_0.contains) [10, 15] = true := by decide +kernel
private theorem cert04_closed_45 : cert04_I_45.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [10, 15] cert04_I_46 cert04_closed_leaf_45 cert04_closed_46
private theorem cert04_closed_leaf_44 : (fun c => (subfaces c).all cert04_I_0.contains) [10, 14] = true := by decide +kernel
private theorem cert04_closed_44 : cert04_I_44.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [10, 14] cert04_I_45 cert04_closed_leaf_44 cert04_closed_45
private theorem cert04_closed_leaf_43 : (fun c => (subfaces c).all cert04_I_0.contains) [10, 11] = true := by decide +kernel
private theorem cert04_closed_43 : cert04_I_43.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [10, 11] cert04_I_44 cert04_closed_leaf_43 cert04_closed_44
private theorem cert04_closed_leaf_42 : (fun c => (subfaces c).all cert04_I_0.contains) [11, 19] = true := by decide +kernel
private theorem cert04_closed_42 : cert04_I_42.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [11, 19] cert04_I_43 cert04_closed_leaf_42 cert04_closed_43
private theorem cert04_closed_leaf_41 : (fun c => (subfaces c).all cert04_I_0.contains) [11, 15] = true := by decide +kernel
private theorem cert04_closed_41 : cert04_I_41.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [11, 15] cert04_I_42 cert04_closed_leaf_41 cert04_closed_42
private theorem cert04_closed_leaf_40 : (fun c => (subfaces c).all cert04_I_0.contains) [12, 13, 19] = true := by decide +kernel
private theorem cert04_closed_40 : cert04_I_40.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [12, 13, 19] cert04_I_41 cert04_closed_leaf_40 cert04_closed_41
private theorem cert04_closed_leaf_39 : (fun c => (subfaces c).all cert04_I_0.contains) [12, 13, 15] = true := by decide +kernel
private theorem cert04_closed_39 : cert04_I_39.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [12, 13, 15] cert04_I_40 cert04_closed_leaf_39 cert04_closed_40
private theorem cert04_closed_leaf_38 : (fun c => (subfaces c).all cert04_I_0.contains) [12, 14, 19] = true := by decide +kernel
private theorem cert04_closed_38 : cert04_I_38.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [12, 14, 19] cert04_I_39 cert04_closed_leaf_38 cert04_closed_39
private theorem cert04_closed_leaf_37 : (fun c => (subfaces c).all cert04_I_0.contains) [12, 14, 15] = true := by decide +kernel
private theorem cert04_closed_37 : cert04_I_37.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [12, 14, 15] cert04_I_38 cert04_closed_leaf_37 cert04_closed_38
private theorem cert04_closed_leaf_36 : (fun c => (subfaces c).all cert04_I_0.contains) [12, 19] = true := by decide +kernel
private theorem cert04_closed_36 : cert04_I_36.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [12, 19] cert04_I_37 cert04_closed_leaf_36 cert04_closed_37
private theorem cert04_closed_leaf_35 : (fun c => (subfaces c).all cert04_I_0.contains) [12, 15] = true := by decide +kernel
private theorem cert04_closed_35 : cert04_I_35.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [12, 15] cert04_I_36 cert04_closed_leaf_35 cert04_closed_36
private theorem cert04_closed_leaf_34 : (fun c => (subfaces c).all cert04_I_0.contains) [12, 14] = true := by decide +kernel
private theorem cert04_closed_34 : cert04_I_34.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [12, 14] cert04_I_35 cert04_closed_leaf_34 cert04_closed_35
private theorem cert04_closed_leaf_33 : (fun c => (subfaces c).all cert04_I_0.contains) [12, 13] = true := by decide +kernel
private theorem cert04_closed_33 : cert04_I_33.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [12, 13] cert04_I_34 cert04_closed_leaf_33 cert04_closed_34
private theorem cert04_closed_leaf_32 : (fun c => (subfaces c).all cert04_I_0.contains) [13, 19] = true := by decide +kernel
private theorem cert04_closed_32 : cert04_I_32.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [13, 19] cert04_I_33 cert04_closed_leaf_32 cert04_closed_33
private theorem cert04_closed_leaf_31 : (fun c => (subfaces c).all cert04_I_0.contains) [13, 15] = true := by decide +kernel
private theorem cert04_closed_31 : cert04_I_31.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [13, 15] cert04_I_32 cert04_closed_leaf_31 cert04_closed_32
private theorem cert04_closed_leaf_30 : (fun c => (subfaces c).all cert04_I_0.contains) [14, 19] = true := by decide +kernel
private theorem cert04_closed_30 : cert04_I_30.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [14, 19] cert04_I_31 cert04_closed_leaf_30 cert04_closed_31
private theorem cert04_closed_leaf_29 : (fun c => (subfaces c).all cert04_I_0.contains) [14, 15] = true := by decide +kernel
private theorem cert04_closed_29 : cert04_I_29.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [14, 15] cert04_I_30 cert04_closed_leaf_29 cert04_closed_30
private theorem cert04_closed_leaf_28 : (fun c => (subfaces c).all cert04_I_0.contains) [16, 17, 19] = true := by decide +kernel
private theorem cert04_closed_28 : cert04_I_28.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [16, 17, 19] cert04_I_29 cert04_closed_leaf_28 cert04_closed_29
private theorem cert04_closed_leaf_27 : (fun c => (subfaces c).all cert04_I_0.contains) [16, 17, 18] = true := by decide +kernel
private theorem cert04_closed_27 : cert04_I_27.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [16, 17, 18] cert04_I_28 cert04_closed_leaf_27 cert04_closed_28
private theorem cert04_closed_leaf_26 : (fun c => (subfaces c).all cert04_I_0.contains) [16, 18, 19] = true := by decide +kernel
private theorem cert04_closed_26 : cert04_I_26.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [16, 18, 19] cert04_I_27 cert04_closed_leaf_26 cert04_closed_27
private theorem cert04_closed_leaf_25 : (fun c => (subfaces c).all cert04_I_0.contains) [16, 19] = true := by decide +kernel
private theorem cert04_closed_25 : cert04_I_25.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [16, 19] cert04_I_26 cert04_closed_leaf_25 cert04_closed_26
private theorem cert04_closed_leaf_24 : (fun c => (subfaces c).all cert04_I_0.contains) [16, 18] = true := by decide +kernel
private theorem cert04_closed_24 : cert04_I_24.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [16, 18] cert04_I_25 cert04_closed_leaf_24 cert04_closed_25
private theorem cert04_closed_leaf_23 : (fun c => (subfaces c).all cert04_I_0.contains) [16, 17] = true := by decide +kernel
private theorem cert04_closed_23 : cert04_I_23.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [16, 17] cert04_I_24 cert04_closed_leaf_23 cert04_closed_24
private theorem cert04_closed_leaf_22 : (fun c => (subfaces c).all cert04_I_0.contains) [17, 18, 19] = true := by decide +kernel
private theorem cert04_closed_22 : cert04_I_22.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [17, 18, 19] cert04_I_23 cert04_closed_leaf_22 cert04_closed_23
private theorem cert04_closed_leaf_21 : (fun c => (subfaces c).all cert04_I_0.contains) [17, 19] = true := by decide +kernel
private theorem cert04_closed_21 : cert04_I_21.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [17, 19] cert04_I_22 cert04_closed_leaf_21 cert04_closed_22
private theorem cert04_closed_leaf_20 : (fun c => (subfaces c).all cert04_I_0.contains) [17, 18] = true := by decide +kernel
private theorem cert04_closed_20 : cert04_I_20.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [17, 18] cert04_I_21 cert04_closed_leaf_20 cert04_closed_21
private theorem cert04_closed_leaf_19 : (fun c => (subfaces c).all cert04_I_0.contains) [18, 19] = true := by decide +kernel
private theorem cert04_closed_19 : cert04_I_19.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [18, 19] cert04_I_20 cert04_closed_leaf_19 cert04_closed_20
private theorem cert04_closed_leaf_18 : (fun c => (subfaces c).all cert04_I_0.contains) [19] = true := by decide +kernel
private theorem cert04_closed_18 : cert04_I_18.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [19] cert04_I_19 cert04_closed_leaf_18 cert04_closed_19
private theorem cert04_closed_leaf_17 : (fun c => (subfaces c).all cert04_I_0.contains) [18] = true := by decide +kernel
private theorem cert04_closed_17 : cert04_I_17.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [18] cert04_I_18 cert04_closed_leaf_17 cert04_closed_18
private theorem cert04_closed_leaf_16 : (fun c => (subfaces c).all cert04_I_0.contains) [17] = true := by decide +kernel
private theorem cert04_closed_16 : cert04_I_16.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [17] cert04_I_17 cert04_closed_leaf_16 cert04_closed_17
private theorem cert04_closed_leaf_15 : (fun c => (subfaces c).all cert04_I_0.contains) [16] = true := by decide +kernel
private theorem cert04_closed_15 : cert04_I_15.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [16] cert04_I_16 cert04_closed_leaf_15 cert04_closed_16
private theorem cert04_closed_leaf_14 : (fun c => (subfaces c).all cert04_I_0.contains) [15] = true := by decide +kernel
private theorem cert04_closed_14 : cert04_I_14.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [15] cert04_I_15 cert04_closed_leaf_14 cert04_closed_15
private theorem cert04_closed_leaf_13 : (fun c => (subfaces c).all cert04_I_0.contains) [14] = true := by decide +kernel
private theorem cert04_closed_13 : cert04_I_13.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [14] cert04_I_14 cert04_closed_leaf_13 cert04_closed_14
private theorem cert04_closed_leaf_12 : (fun c => (subfaces c).all cert04_I_0.contains) [13] = true := by decide +kernel
private theorem cert04_closed_12 : cert04_I_12.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [13] cert04_I_13 cert04_closed_leaf_12 cert04_closed_13
private theorem cert04_closed_leaf_11 : (fun c => (subfaces c).all cert04_I_0.contains) [12] = true := by decide +kernel
private theorem cert04_closed_11 : cert04_I_11.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [12] cert04_I_12 cert04_closed_leaf_11 cert04_closed_12
private theorem cert04_closed_leaf_10 : (fun c => (subfaces c).all cert04_I_0.contains) [11] = true := by decide +kernel
private theorem cert04_closed_10 : cert04_I_10.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [11] cert04_I_11 cert04_closed_leaf_10 cert04_closed_11
private theorem cert04_closed_leaf_9 : (fun c => (subfaces c).all cert04_I_0.contains) [10] = true := by decide +kernel
private theorem cert04_closed_9 : cert04_I_9.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [10] cert04_I_10 cert04_closed_leaf_9 cert04_closed_10
private theorem cert04_closed_leaf_8 : (fun c => (subfaces c).all cert04_I_0.contains) [9] = true := by decide +kernel
private theorem cert04_closed_8 : cert04_I_8.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [9] cert04_I_9 cert04_closed_leaf_8 cert04_closed_9
private theorem cert04_closed_leaf_7 : (fun c => (subfaces c).all cert04_I_0.contains) [8] = true := by decide +kernel
private theorem cert04_closed_7 : cert04_I_7.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [8] cert04_I_8 cert04_closed_leaf_7 cert04_closed_8
private theorem cert04_closed_leaf_6 : (fun c => (subfaces c).all cert04_I_0.contains) [7] = true := by decide +kernel
private theorem cert04_closed_6 : cert04_I_6.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [7] cert04_I_7 cert04_closed_leaf_6 cert04_closed_7
private theorem cert04_closed_leaf_5 : (fun c => (subfaces c).all cert04_I_0.contains) [6] = true := by decide +kernel
private theorem cert04_closed_5 : cert04_I_5.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [6] cert04_I_6 cert04_closed_leaf_5 cert04_closed_6
private theorem cert04_closed_leaf_4 : (fun c => (subfaces c).all cert04_I_0.contains) [5] = true := by decide +kernel
private theorem cert04_closed_4 : cert04_I_4.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [5] cert04_I_5 cert04_closed_leaf_4 cert04_closed_5
private theorem cert04_closed_leaf_3 : (fun c => (subfaces c).all cert04_I_0.contains) [4] = true := by decide +kernel
private theorem cert04_closed_3 : cert04_I_3.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [4] cert04_I_4 cert04_closed_leaf_3 cert04_closed_4
private theorem cert04_closed_leaf_2 : (fun c => (subfaces c).all cert04_I_0.contains) [3] = true := by decide +kernel
private theorem cert04_closed_2 : cert04_I_2.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [3] cert04_I_3 cert04_closed_leaf_2 cert04_closed_3
private theorem cert04_closed_leaf_1 : (fun c => (subfaces c).all cert04_I_0.contains) [2] = true := by decide +kernel
private theorem cert04_closed_1 : cert04_I_1.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [2] cert04_I_2 cert04_closed_leaf_1 cert04_closed_2
private theorem cert04_closed_leaf_0 : (fun c => (subfaces c).all cert04_I_0.contains) [1] = true := by decide +kernel
private theorem cert04_closed_0 : cert04_I_0.all (fun c => (subfaces c).all cert04_I_0.contains) = true :=
  cert04_all_cons (fun c => (subfaces c).all cert04_I_0.contains) [1] cert04_I_1 cert04_closed_leaf_0 cert04_closed_1
private theorem cert04_forward_391 : cert04_L_391.all (cert04_U_0.contains) = true := rfl
private theorem cert04_forward_leaf_390 : (cert04_U_0.contains) [16, 17, 18, 19] = true := by decide +kernel
private theorem cert04_forward_390 : cert04_L_390.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [16, 17, 18, 19] cert04_L_391 cert04_forward_leaf_390 cert04_forward_391
private theorem cert04_forward_leaf_389 : (cert04_U_0.contains) [1, 16, 17, 18, 19] = true := by decide +kernel
private theorem cert04_forward_389 : cert04_L_389.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 16, 17, 18, 19] cert04_L_390 cert04_forward_leaf_389 cert04_forward_390
private theorem cert04_forward_leaf_388 : (cert04_U_0.contains) [1, 17, 18, 19] = true := by decide +kernel
private theorem cert04_forward_388 : cert04_L_388.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 17, 18, 19] cert04_L_389 cert04_forward_leaf_388 cert04_forward_389
private theorem cert04_forward_leaf_387 : (cert04_U_0.contains) [1, 3, 17, 18, 19] = true := by decide +kernel
private theorem cert04_forward_387 : cert04_L_387.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 17, 18, 19] cert04_L_388 cert04_forward_leaf_387 cert04_forward_388
private theorem cert04_forward_leaf_386 : (cert04_U_0.contains) [3, 17, 18, 19] = true := by decide +kernel
private theorem cert04_forward_386 : cert04_L_386.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 17, 18, 19] cert04_L_387 cert04_forward_leaf_386 cert04_forward_387
private theorem cert04_forward_leaf_385 : (cert04_U_0.contains) [2, 3, 17, 18, 19] = true := by decide +kernel
private theorem cert04_forward_385 : cert04_L_385.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 17, 18, 19] cert04_L_386 cert04_forward_leaf_385 cert04_forward_386
private theorem cert04_forward_leaf_384 : (cert04_U_0.contains) [2, 3, 18, 19] = true := by decide +kernel
private theorem cert04_forward_384 : cert04_L_384.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 18, 19] cert04_L_385 cert04_forward_leaf_384 cert04_forward_385
private theorem cert04_forward_leaf_383 : (cert04_U_0.contains) [2, 3, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_383 : cert04_L_383.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 7, 18, 19] cert04_L_384 cert04_forward_leaf_383 cert04_forward_384
private theorem cert04_forward_leaf_382 : (cert04_U_0.contains) [2, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_382 : cert04_L_382.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 7, 18, 19] cert04_L_383 cert04_forward_leaf_382 cert04_forward_383
private theorem cert04_forward_leaf_381 : (cert04_U_0.contains) [2, 6, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_381 : cert04_L_381.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 7, 18, 19] cert04_L_382 cert04_forward_leaf_381 cert04_forward_382
private theorem cert04_forward_leaf_380 : (cert04_U_0.contains) [6, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_380 : cert04_L_380.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 7, 18, 19] cert04_L_381 cert04_forward_leaf_380 cert04_forward_381
private theorem cert04_forward_leaf_379 : (cert04_U_0.contains) [4, 6, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_379 : cert04_L_379.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 7, 18, 19] cert04_L_380 cert04_forward_leaf_379 cert04_forward_380
private theorem cert04_forward_leaf_378 : (cert04_U_0.contains) [4, 6, 7, 19] = true := by decide +kernel
private theorem cert04_forward_378 : cert04_L_378.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 7, 19] cert04_L_379 cert04_forward_leaf_378 cert04_forward_379
private theorem cert04_forward_leaf_377 : (cert04_U_0.contains) [4, 6, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_377 : cert04_L_377.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 7, 15, 19] cert04_L_378 cert04_forward_leaf_377 cert04_forward_378
private theorem cert04_forward_leaf_376 : (cert04_U_0.contains) [4, 6, 15, 19] = true := by decide +kernel
private theorem cert04_forward_376 : cert04_L_376.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 15, 19] cert04_L_377 cert04_forward_leaf_376 cert04_forward_377
private theorem cert04_forward_leaf_375 : (cert04_U_0.contains) [4, 6, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_375 : cert04_L_375.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 14, 15, 19] cert04_L_376 cert04_forward_leaf_375 cert04_forward_376
private theorem cert04_forward_leaf_374 : (cert04_U_0.contains) [4, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_374 : cert04_L_374.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 14, 15, 19] cert04_L_375 cert04_forward_leaf_374 cert04_forward_375
private theorem cert04_forward_leaf_373 : (cert04_U_0.contains) [4, 12, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_373 : cert04_L_373.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12, 14, 15, 19] cert04_L_374 cert04_forward_leaf_373 cert04_forward_374
private theorem cert04_forward_leaf_372 : (cert04_U_0.contains) [12, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_372 : cert04_L_372.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12, 14, 15, 19] cert04_L_373 cert04_forward_leaf_372 cert04_forward_373
private theorem cert04_forward_leaf_371 : (cert04_U_0.contains) [8, 12, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_371 : cert04_L_371.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12, 14, 15, 19] cert04_L_372 cert04_forward_leaf_371 cert04_forward_372
private theorem cert04_forward_leaf_370 : (cert04_U_0.contains) [8, 12, 15, 19] = true := by decide +kernel
private theorem cert04_forward_370 : cert04_L_370.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12, 15, 19] cert04_L_371 cert04_forward_leaf_370 cert04_forward_371
private theorem cert04_forward_leaf_369 : (cert04_U_0.contains) [8, 12, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_369 : cert04_L_369.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12, 13, 15, 19] cert04_L_370 cert04_forward_leaf_369 cert04_forward_370
private theorem cert04_forward_leaf_368 : (cert04_U_0.contains) [8, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_368 : cert04_L_368.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 14, 15, 19] cert04_L_369 cert04_forward_leaf_368 cert04_forward_369
private theorem cert04_forward_leaf_367 : (cert04_U_0.contains) [8, 10, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_367 : cert04_L_367.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10, 14, 15, 19] cert04_L_368 cert04_forward_leaf_367 cert04_forward_368
private theorem cert04_forward_leaf_366 : (cert04_U_0.contains) [8, 10, 15, 19] = true := by decide +kernel
private theorem cert04_forward_366 : cert04_L_366.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10, 15, 19] cert04_L_367 cert04_forward_leaf_366 cert04_forward_367
private theorem cert04_forward_leaf_365 : (cert04_U_0.contains) [8, 10, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_365 : cert04_L_365.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10, 11, 15, 19] cert04_L_366 cert04_forward_leaf_365 cert04_forward_366
private theorem cert04_forward_leaf_364 : (cert04_U_0.contains) [8, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_364 : cert04_L_364.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 13, 15, 19] cert04_L_365 cert04_forward_leaf_364 cert04_forward_365
private theorem cert04_forward_leaf_363 : (cert04_U_0.contains) [8, 9, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_363 : cert04_L_363.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9, 13, 15, 19] cert04_L_364 cert04_forward_leaf_363 cert04_forward_364
private theorem cert04_forward_leaf_362 : (cert04_U_0.contains) [8, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_362 : cert04_L_362.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 11, 15, 19] cert04_L_363 cert04_forward_leaf_362 cert04_forward_363
private theorem cert04_forward_leaf_361 : (cert04_U_0.contains) [8, 9, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_361 : cert04_L_361.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9, 11, 15, 19] cert04_L_362 cert04_forward_leaf_361 cert04_forward_362
private theorem cert04_forward_leaf_360 : (cert04_U_0.contains) [12, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_360 : cert04_L_360.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12, 13, 15, 19] cert04_L_361 cert04_forward_leaf_360 cert04_forward_361
private theorem cert04_forward_leaf_359 : (cert04_U_0.contains) [4, 12, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_359 : cert04_L_359.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12, 13, 15, 19] cert04_L_360 cert04_forward_leaf_359 cert04_forward_360
private theorem cert04_forward_leaf_358 : (cert04_U_0.contains) [4, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_358 : cert04_L_358.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 13, 15, 19] cert04_L_359 cert04_forward_leaf_358 cert04_forward_359
private theorem cert04_forward_leaf_357 : (cert04_U_0.contains) [4, 5, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_357 : cert04_L_357.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 13, 15, 19] cert04_L_358 cert04_forward_leaf_357 cert04_forward_358
private theorem cert04_forward_leaf_356 : (cert04_U_0.contains) [4, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_356 : cert04_L_356.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 7, 18, 19] cert04_L_357 cert04_forward_leaf_356 cert04_forward_357
private theorem cert04_forward_leaf_355 : (cert04_U_0.contains) [4, 5, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_355 : cert04_L_355.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 7, 18, 19] cert04_L_356 cert04_forward_leaf_355 cert04_forward_356
private theorem cert04_forward_leaf_354 : (cert04_U_0.contains) [4, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_354 : cert04_L_354.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 7, 15, 19] cert04_L_355 cert04_forward_leaf_354 cert04_forward_355
private theorem cert04_forward_leaf_353 : (cert04_U_0.contains) [4, 5, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_353 : cert04_L_353.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 7, 15, 19] cert04_L_354 cert04_forward_leaf_353 cert04_forward_354
private theorem cert04_forward_leaf_352 : (cert04_U_0.contains) [10, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_352 : cert04_L_352.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10, 14, 15, 19] cert04_L_353 cert04_forward_leaf_352 cert04_forward_353
private theorem cert04_forward_leaf_351 : (cert04_U_0.contains) [2, 10, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_351 : cert04_L_351.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10, 14, 15, 19] cert04_L_352 cert04_forward_leaf_351 cert04_forward_352
private theorem cert04_forward_leaf_350 : (cert04_U_0.contains) [10, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_350 : cert04_L_350.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10, 11, 15, 19] cert04_L_351 cert04_forward_leaf_350 cert04_forward_351
private theorem cert04_forward_leaf_349 : (cert04_U_0.contains) [2, 10, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_349 : cert04_L_349.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10, 11, 15, 19] cert04_L_350 cert04_forward_leaf_349 cert04_forward_350
private theorem cert04_forward_leaf_348 : (cert04_U_0.contains) [6, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_348 : cert04_L_348.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 14, 15, 19] cert04_L_349 cert04_forward_leaf_348 cert04_forward_349
private theorem cert04_forward_leaf_347 : (cert04_U_0.contains) [2, 6, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_347 : cert04_L_347.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 14, 15, 19] cert04_L_348 cert04_forward_leaf_347 cert04_forward_348
private theorem cert04_forward_leaf_346 : (cert04_U_0.contains) [6, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_346 : cert04_L_346.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 7, 15, 19] cert04_L_347 cert04_forward_leaf_346 cert04_forward_347
private theorem cert04_forward_leaf_345 : (cert04_U_0.contains) [2, 6, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_345 : cert04_L_345.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 7, 15, 19] cert04_L_346 cert04_forward_leaf_345 cert04_forward_346
private theorem cert04_forward_leaf_344 : (cert04_U_0.contains) [2, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_344 : cert04_L_344.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 11, 15, 19] cert04_L_345 cert04_forward_leaf_344 cert04_forward_345
private theorem cert04_forward_leaf_343 : (cert04_U_0.contains) [2, 3, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_343 : cert04_L_343.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 11, 15, 19] cert04_L_344 cert04_forward_leaf_343 cert04_forward_344
private theorem cert04_forward_leaf_342 : (cert04_U_0.contains) [2, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_342 : cert04_L_342.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 7, 15, 19] cert04_L_343 cert04_forward_leaf_342 cert04_forward_343
private theorem cert04_forward_leaf_341 : (cert04_U_0.contains) [2, 3, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_341 : cert04_L_341.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 7, 15, 19] cert04_L_342 cert04_forward_leaf_341 cert04_forward_342
private theorem cert04_forward_leaf_340 : (cert04_U_0.contains) [9, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_340 : cert04_L_340.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9, 13, 15, 19] cert04_L_341 cert04_forward_leaf_340 cert04_forward_341
private theorem cert04_forward_leaf_339 : (cert04_U_0.contains) [1, 9, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_339 : cert04_L_339.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9, 13, 15, 19] cert04_L_340 cert04_forward_leaf_339 cert04_forward_340
private theorem cert04_forward_leaf_338 : (cert04_U_0.contains) [9, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_338 : cert04_L_338.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9, 11, 15, 19] cert04_L_339 cert04_forward_leaf_338 cert04_forward_339
private theorem cert04_forward_leaf_337 : (cert04_U_0.contains) [1, 9, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_337 : cert04_L_337.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9, 11, 15, 19] cert04_L_338 cert04_forward_leaf_337 cert04_forward_338
private theorem cert04_forward_leaf_336 : (cert04_U_0.contains) [5, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_336 : cert04_L_336.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 13, 15, 19] cert04_L_337 cert04_forward_leaf_336 cert04_forward_337
private theorem cert04_forward_leaf_335 : (cert04_U_0.contains) [1, 5, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_335 : cert04_L_335.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 13, 15, 19] cert04_L_336 cert04_forward_leaf_335 cert04_forward_336
private theorem cert04_forward_leaf_334 : (cert04_U_0.contains) [5, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_334 : cert04_L_334.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 7, 18, 19] cert04_L_335 cert04_forward_leaf_334 cert04_forward_335
private theorem cert04_forward_leaf_333 : (cert04_U_0.contains) [1, 5, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_333 : cert04_L_333.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 7, 18, 19] cert04_L_334 cert04_forward_leaf_333 cert04_forward_334
private theorem cert04_forward_leaf_332 : (cert04_U_0.contains) [5, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_332 : cert04_L_332.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 7, 15, 19] cert04_L_333 cert04_forward_leaf_332 cert04_forward_333
private theorem cert04_forward_leaf_331 : (cert04_U_0.contains) [1, 5, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_331 : cert04_L_331.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 7, 15, 19] cert04_L_332 cert04_forward_leaf_331 cert04_forward_332
private theorem cert04_forward_leaf_330 : (cert04_U_0.contains) [3, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_330 : cert04_L_330.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 11, 15, 19] cert04_L_331 cert04_forward_leaf_330 cert04_forward_331
private theorem cert04_forward_leaf_329 : (cert04_U_0.contains) [1, 3, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_329 : cert04_L_329.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 11, 15, 19] cert04_L_330 cert04_forward_leaf_329 cert04_forward_330
private theorem cert04_forward_leaf_328 : (cert04_U_0.contains) [3, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_328 : cert04_L_328.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 7, 18, 19] cert04_L_329 cert04_forward_leaf_328 cert04_forward_329
private theorem cert04_forward_leaf_327 : (cert04_U_0.contains) [1, 3, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_327 : cert04_L_327.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 7, 18, 19] cert04_L_328 cert04_forward_leaf_327 cert04_forward_328
private theorem cert04_forward_leaf_326 : (cert04_U_0.contains) [3, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_326 : cert04_L_326.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 7, 15, 19] cert04_L_327 cert04_forward_leaf_326 cert04_forward_327
private theorem cert04_forward_leaf_325 : (cert04_U_0.contains) [1, 3, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_325 : cert04_L_325.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 7, 15, 19] cert04_L_326 cert04_forward_leaf_325 cert04_forward_326
private theorem cert04_forward_leaf_324 : (cert04_U_0.contains) [8, 15, 19] = true := by decide +kernel
private theorem cert04_forward_324 : cert04_L_324.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 15, 19] cert04_L_325 cert04_forward_leaf_324 cert04_forward_325
private theorem cert04_forward_leaf_323 : (cert04_U_0.contains) [8, 9, 15, 19] = true := by decide +kernel
private theorem cert04_forward_323 : cert04_L_323.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9, 15, 19] cert04_L_324 cert04_forward_leaf_323 cert04_forward_324
private theorem cert04_forward_leaf_322 : (cert04_U_0.contains) [12, 15, 19] = true := by decide +kernel
private theorem cert04_forward_322 : cert04_L_322.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12, 15, 19] cert04_L_323 cert04_forward_leaf_322 cert04_forward_323
private theorem cert04_forward_leaf_321 : (cert04_U_0.contains) [4, 12, 15, 19] = true := by decide +kernel
private theorem cert04_forward_321 : cert04_L_321.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12, 15, 19] cert04_L_322 cert04_forward_leaf_321 cert04_forward_322
private theorem cert04_forward_leaf_320 : (cert04_U_0.contains) [4, 15, 19] = true := by decide +kernel
private theorem cert04_forward_320 : cert04_L_320.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 15, 19] cert04_L_321 cert04_forward_leaf_320 cert04_forward_321
private theorem cert04_forward_leaf_319 : (cert04_U_0.contains) [4, 5, 15, 19] = true := by decide +kernel
private theorem cert04_forward_319 : cert04_L_319.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 15, 19] cert04_L_320 cert04_forward_leaf_319 cert04_forward_320
private theorem cert04_forward_leaf_318 : (cert04_U_0.contains) [4, 7, 19] = true := by decide +kernel
private theorem cert04_forward_318 : cert04_L_318.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 7, 19] cert04_L_319 cert04_forward_leaf_318 cert04_forward_319
private theorem cert04_forward_leaf_317 : (cert04_U_0.contains) [4, 5, 7, 19] = true := by decide +kernel
private theorem cert04_forward_317 : cert04_L_317.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 7, 19] cert04_L_318 cert04_forward_leaf_317 cert04_forward_318
private theorem cert04_forward_leaf_316 : (cert04_U_0.contains) [14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_316 : cert04_L_316.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [14, 15, 19] cert04_L_317 cert04_forward_leaf_316 cert04_forward_317
private theorem cert04_forward_leaf_315 : (cert04_U_0.contains) [2, 14, 15, 19] = true := by decide +kernel
private theorem cert04_forward_315 : cert04_L_315.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 14, 15, 19] cert04_L_316 cert04_forward_leaf_315 cert04_forward_316
private theorem cert04_forward_leaf_314 : (cert04_U_0.contains) [10, 15, 19] = true := by decide +kernel
private theorem cert04_forward_314 : cert04_L_314.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10, 15, 19] cert04_L_315 cert04_forward_leaf_314 cert04_forward_315
private theorem cert04_forward_leaf_313 : (cert04_U_0.contains) [2, 10, 15, 19] = true := by decide +kernel
private theorem cert04_forward_313 : cert04_L_313.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10, 15, 19] cert04_L_314 cert04_forward_leaf_313 cert04_forward_314
private theorem cert04_forward_leaf_312 : (cert04_U_0.contains) [6, 15, 19] = true := by decide +kernel
private theorem cert04_forward_312 : cert04_L_312.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 15, 19] cert04_L_313 cert04_forward_leaf_312 cert04_forward_313
private theorem cert04_forward_leaf_311 : (cert04_U_0.contains) [2, 6, 15, 19] = true := by decide +kernel
private theorem cert04_forward_311 : cert04_L_311.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 15, 19] cert04_L_312 cert04_forward_leaf_311 cert04_forward_312
private theorem cert04_forward_leaf_310 : (cert04_U_0.contains) [6, 7, 19] = true := by decide +kernel
private theorem cert04_forward_310 : cert04_L_310.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 7, 19] cert04_L_311 cert04_forward_leaf_310 cert04_forward_311
private theorem cert04_forward_leaf_309 : (cert04_U_0.contains) [2, 6, 7, 19] = true := by decide +kernel
private theorem cert04_forward_309 : cert04_L_309.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 7, 19] cert04_L_310 cert04_forward_leaf_309 cert04_forward_310
private theorem cert04_forward_leaf_308 : (cert04_U_0.contains) [2, 15, 19] = true := by decide +kernel
private theorem cert04_forward_308 : cert04_L_308.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 15, 19] cert04_L_309 cert04_forward_leaf_308 cert04_forward_309
private theorem cert04_forward_leaf_307 : (cert04_U_0.contains) [2, 3, 15, 19] = true := by decide +kernel
private theorem cert04_forward_307 : cert04_L_307.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 15, 19] cert04_L_308 cert04_forward_leaf_307 cert04_forward_308
private theorem cert04_forward_leaf_306 : (cert04_U_0.contains) [2, 7, 19] = true := by decide +kernel
private theorem cert04_forward_306 : cert04_L_306.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 7, 19] cert04_L_307 cert04_forward_leaf_306 cert04_forward_307
private theorem cert04_forward_leaf_305 : (cert04_U_0.contains) [2, 3, 7, 19] = true := by decide +kernel
private theorem cert04_forward_305 : cert04_L_305.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 7, 19] cert04_L_306 cert04_forward_leaf_305 cert04_forward_306
private theorem cert04_forward_leaf_304 : (cert04_U_0.contains) [13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_304 : cert04_L_304.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [13, 15, 19] cert04_L_305 cert04_forward_leaf_304 cert04_forward_305
private theorem cert04_forward_leaf_303 : (cert04_U_0.contains) [1, 13, 15, 19] = true := by decide +kernel
private theorem cert04_forward_303 : cert04_L_303.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 13, 15, 19] cert04_L_304 cert04_forward_leaf_303 cert04_forward_304
private theorem cert04_forward_leaf_302 : (cert04_U_0.contains) [11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_302 : cert04_L_302.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [11, 15, 19] cert04_L_303 cert04_forward_leaf_302 cert04_forward_303
private theorem cert04_forward_leaf_301 : (cert04_U_0.contains) [1, 11, 15, 19] = true := by decide +kernel
private theorem cert04_forward_301 : cert04_L_301.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 11, 15, 19] cert04_L_302 cert04_forward_leaf_301 cert04_forward_302
private theorem cert04_forward_leaf_300 : (cert04_U_0.contains) [9, 15, 19] = true := by decide +kernel
private theorem cert04_forward_300 : cert04_L_300.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9, 15, 19] cert04_L_301 cert04_forward_leaf_300 cert04_forward_301
private theorem cert04_forward_leaf_299 : (cert04_U_0.contains) [1, 9, 15, 19] = true := by decide +kernel
private theorem cert04_forward_299 : cert04_L_299.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9, 15, 19] cert04_L_300 cert04_forward_leaf_299 cert04_forward_300
private theorem cert04_forward_leaf_298 : (cert04_U_0.contains) [7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_298 : cert04_L_298.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [7, 18, 19] cert04_L_299 cert04_forward_leaf_298 cert04_forward_299
private theorem cert04_forward_leaf_297 : (cert04_U_0.contains) [1, 7, 18, 19] = true := by decide +kernel
private theorem cert04_forward_297 : cert04_L_297.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 7, 18, 19] cert04_L_298 cert04_forward_leaf_297 cert04_forward_298
private theorem cert04_forward_leaf_296 : (cert04_U_0.contains) [7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_296 : cert04_L_296.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [7, 15, 19] cert04_L_297 cert04_forward_leaf_296 cert04_forward_297
private theorem cert04_forward_leaf_295 : (cert04_U_0.contains) [1, 7, 15, 19] = true := by decide +kernel
private theorem cert04_forward_295 : cert04_L_295.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 7, 15, 19] cert04_L_296 cert04_forward_leaf_295 cert04_forward_296
private theorem cert04_forward_leaf_294 : (cert04_U_0.contains) [5, 15, 19] = true := by decide +kernel
private theorem cert04_forward_294 : cert04_L_294.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 15, 19] cert04_L_295 cert04_forward_leaf_294 cert04_forward_295
private theorem cert04_forward_leaf_293 : (cert04_U_0.contains) [1, 5, 15, 19] = true := by decide +kernel
private theorem cert04_forward_293 : cert04_L_293.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 15, 19] cert04_L_294 cert04_forward_leaf_293 cert04_forward_294
private theorem cert04_forward_leaf_292 : (cert04_U_0.contains) [5, 7, 19] = true := by decide +kernel
private theorem cert04_forward_292 : cert04_L_292.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 7, 19] cert04_L_293 cert04_forward_leaf_292 cert04_forward_293
private theorem cert04_forward_leaf_291 : (cert04_U_0.contains) [1, 5, 7, 19] = true := by decide +kernel
private theorem cert04_forward_291 : cert04_L_291.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 7, 19] cert04_L_292 cert04_forward_leaf_291 cert04_forward_292
private theorem cert04_forward_leaf_290 : (cert04_U_0.contains) [3, 18, 19] = true := by decide +kernel
private theorem cert04_forward_290 : cert04_L_290.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 18, 19] cert04_L_291 cert04_forward_leaf_290 cert04_forward_291
private theorem cert04_forward_leaf_289 : (cert04_U_0.contains) [1, 3, 18, 19] = true := by decide +kernel
private theorem cert04_forward_289 : cert04_L_289.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 18, 19] cert04_L_290 cert04_forward_leaf_289 cert04_forward_290
private theorem cert04_forward_leaf_288 : (cert04_U_0.contains) [3, 15, 19] = true := by decide +kernel
private theorem cert04_forward_288 : cert04_L_288.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 15, 19] cert04_L_289 cert04_forward_leaf_288 cert04_forward_289
private theorem cert04_forward_leaf_287 : (cert04_U_0.contains) [1, 3, 15, 19] = true := by decide +kernel
private theorem cert04_forward_287 : cert04_L_287.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 15, 19] cert04_L_288 cert04_forward_leaf_287 cert04_forward_288
private theorem cert04_forward_leaf_286 : (cert04_U_0.contains) [3, 7, 19] = true := by decide +kernel
private theorem cert04_forward_286 : cert04_L_286.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 7, 19] cert04_L_287 cert04_forward_leaf_286 cert04_forward_287
private theorem cert04_forward_leaf_285 : (cert04_U_0.contains) [1, 3, 7, 19] = true := by decide +kernel
private theorem cert04_forward_285 : cert04_L_285.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 7, 19] cert04_L_286 cert04_forward_leaf_285 cert04_forward_286
private theorem cert04_forward_leaf_284 : (cert04_U_0.contains) [15, 19] = true := by decide +kernel
private theorem cert04_forward_284 : cert04_L_284.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [15, 19] cert04_L_285 cert04_forward_leaf_284 cert04_forward_285
private theorem cert04_forward_leaf_283 : (cert04_U_0.contains) [1, 15, 19] = true := by decide +kernel
private theorem cert04_forward_283 : cert04_L_283.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 15, 19] cert04_L_284 cert04_forward_leaf_283 cert04_forward_284
private theorem cert04_forward_leaf_282 : (cert04_U_0.contains) [7, 19] = true := by decide +kernel
private theorem cert04_forward_282 : cert04_L_282.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [7, 19] cert04_L_283 cert04_forward_leaf_282 cert04_forward_283
private theorem cert04_forward_leaf_281 : (cert04_U_0.contains) [1, 7, 19] = true := by decide +kernel
private theorem cert04_forward_281 : cert04_L_281.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 7, 19] cert04_L_282 cert04_forward_leaf_281 cert04_forward_282
private theorem cert04_forward_leaf_280 : (cert04_U_0.contains) [1, 3, 7, 18] = true := by decide +kernel
private theorem cert04_forward_280 : cert04_L_280.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 7, 18] cert04_L_281 cert04_forward_leaf_280 cert04_forward_281
private theorem cert04_forward_leaf_279 : (cert04_U_0.contains) [1, 3, 7, 15] = true := by decide +kernel
private theorem cert04_forward_279 : cert04_L_279.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 7, 15] cert04_L_280 cert04_forward_leaf_279 cert04_forward_280
private theorem cert04_forward_leaf_278 : (cert04_U_0.contains) [1, 3, 11, 19] = true := by decide +kernel
private theorem cert04_forward_278 : cert04_L_278.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 11, 19] cert04_L_279 cert04_forward_leaf_278 cert04_forward_279
private theorem cert04_forward_leaf_277 : (cert04_U_0.contains) [1, 3, 11, 15] = true := by decide +kernel
private theorem cert04_forward_277 : cert04_L_277.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 11, 15] cert04_L_278 cert04_forward_leaf_277 cert04_forward_278
private theorem cert04_forward_leaf_276 : (cert04_U_0.contains) [1, 3, 17, 19] = true := by decide +kernel
private theorem cert04_forward_276 : cert04_L_276.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 17, 19] cert04_L_277 cert04_forward_leaf_276 cert04_forward_277
private theorem cert04_forward_leaf_275 : (cert04_U_0.contains) [1, 3, 17, 18] = true := by decide +kernel
private theorem cert04_forward_275 : cert04_L_275.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 17, 18] cert04_L_276 cert04_forward_leaf_275 cert04_forward_276
private theorem cert04_forward_leaf_274 : (cert04_U_0.contains) [1, 3, 19] = true := by decide +kernel
private theorem cert04_forward_274 : cert04_L_274.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 19] cert04_L_275 cert04_forward_leaf_274 cert04_forward_275
private theorem cert04_forward_leaf_273 : (cert04_U_0.contains) [1, 3, 18] = true := by decide +kernel
private theorem cert04_forward_273 : cert04_L_273.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 18] cert04_L_274 cert04_forward_leaf_273 cert04_forward_274
private theorem cert04_forward_leaf_272 : (cert04_U_0.contains) [1, 3, 17] = true := by decide +kernel
private theorem cert04_forward_272 : cert04_L_272.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 17] cert04_L_273 cert04_forward_leaf_272 cert04_forward_273
private theorem cert04_forward_leaf_271 : (cert04_U_0.contains) [1, 3, 15] = true := by decide +kernel
private theorem cert04_forward_271 : cert04_L_271.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 15] cert04_L_272 cert04_forward_leaf_271 cert04_forward_272
private theorem cert04_forward_leaf_270 : (cert04_U_0.contains) [1, 3, 11] = true := by decide +kernel
private theorem cert04_forward_270 : cert04_L_270.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 11] cert04_L_271 cert04_forward_leaf_270 cert04_forward_271
private theorem cert04_forward_leaf_269 : (cert04_U_0.contains) [1, 3, 7] = true := by decide +kernel
private theorem cert04_forward_269 : cert04_L_269.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3, 7] cert04_L_270 cert04_forward_leaf_269 cert04_forward_270
private theorem cert04_forward_leaf_268 : (cert04_U_0.contains) [1, 5, 7, 18] = true := by decide +kernel
private theorem cert04_forward_268 : cert04_L_268.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 7, 18] cert04_L_269 cert04_forward_leaf_268 cert04_forward_269
private theorem cert04_forward_leaf_267 : (cert04_U_0.contains) [1, 5, 7, 15] = true := by decide +kernel
private theorem cert04_forward_267 : cert04_L_267.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 7, 15] cert04_L_268 cert04_forward_leaf_267 cert04_forward_268
private theorem cert04_forward_leaf_266 : (cert04_U_0.contains) [1, 5, 13, 19] = true := by decide +kernel
private theorem cert04_forward_266 : cert04_L_266.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 13, 19] cert04_L_267 cert04_forward_leaf_266 cert04_forward_267
private theorem cert04_forward_leaf_265 : (cert04_U_0.contains) [1, 5, 13, 15] = true := by decide +kernel
private theorem cert04_forward_265 : cert04_L_265.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 13, 15] cert04_L_266 cert04_forward_leaf_265 cert04_forward_266
private theorem cert04_forward_leaf_264 : (cert04_U_0.contains) [1, 5, 18, 19] = true := by decide +kernel
private theorem cert04_forward_264 : cert04_L_264.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 18, 19] cert04_L_265 cert04_forward_leaf_264 cert04_forward_265
private theorem cert04_forward_leaf_263 : (cert04_U_0.contains) [1, 5, 19] = true := by decide +kernel
private theorem cert04_forward_263 : cert04_L_263.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 19] cert04_L_264 cert04_forward_leaf_263 cert04_forward_264
private theorem cert04_forward_leaf_262 : (cert04_U_0.contains) [1, 5, 18] = true := by decide +kernel
private theorem cert04_forward_262 : cert04_L_262.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 18] cert04_L_263 cert04_forward_leaf_262 cert04_forward_263
private theorem cert04_forward_leaf_261 : (cert04_U_0.contains) [1, 5, 15] = true := by decide +kernel
private theorem cert04_forward_261 : cert04_L_261.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 15] cert04_L_262 cert04_forward_leaf_261 cert04_forward_262
private theorem cert04_forward_leaf_260 : (cert04_U_0.contains) [1, 5, 13] = true := by decide +kernel
private theorem cert04_forward_260 : cert04_L_260.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 13] cert04_L_261 cert04_forward_leaf_260 cert04_forward_261
private theorem cert04_forward_leaf_259 : (cert04_U_0.contains) [1, 5, 7] = true := by decide +kernel
private theorem cert04_forward_259 : cert04_L_259.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5, 7] cert04_L_260 cert04_forward_leaf_259 cert04_forward_260
private theorem cert04_forward_leaf_258 : (cert04_U_0.contains) [1, 7, 18] = true := by decide +kernel
private theorem cert04_forward_258 : cert04_L_258.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 7, 18] cert04_L_259 cert04_forward_leaf_258 cert04_forward_259
private theorem cert04_forward_leaf_257 : (cert04_U_0.contains) [1, 7, 15] = true := by decide +kernel
private theorem cert04_forward_257 : cert04_L_257.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 7, 15] cert04_L_258 cert04_forward_leaf_257 cert04_forward_258
private theorem cert04_forward_leaf_256 : (cert04_U_0.contains) [1, 9, 11, 19] = true := by decide +kernel
private theorem cert04_forward_256 : cert04_L_256.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9, 11, 19] cert04_L_257 cert04_forward_leaf_256 cert04_forward_257
private theorem cert04_forward_leaf_255 : (cert04_U_0.contains) [1, 9, 11, 15] = true := by decide +kernel
private theorem cert04_forward_255 : cert04_L_255.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9, 11, 15] cert04_L_256 cert04_forward_leaf_255 cert04_forward_256
private theorem cert04_forward_leaf_254 : (cert04_U_0.contains) [1, 9, 13, 19] = true := by decide +kernel
private theorem cert04_forward_254 : cert04_L_254.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9, 13, 19] cert04_L_255 cert04_forward_leaf_254 cert04_forward_255
private theorem cert04_forward_leaf_253 : (cert04_U_0.contains) [1, 9, 13, 15] = true := by decide +kernel
private theorem cert04_forward_253 : cert04_L_253.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9, 13, 15] cert04_L_254 cert04_forward_leaf_253 cert04_forward_254
private theorem cert04_forward_leaf_252 : (cert04_U_0.contains) [1, 9, 19] = true := by decide +kernel
private theorem cert04_forward_252 : cert04_L_252.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9, 19] cert04_L_253 cert04_forward_leaf_252 cert04_forward_253
private theorem cert04_forward_leaf_251 : (cert04_U_0.contains) [1, 9, 15] = true := by decide +kernel
private theorem cert04_forward_251 : cert04_L_251.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9, 15] cert04_L_252 cert04_forward_leaf_251 cert04_forward_252
private theorem cert04_forward_leaf_250 : (cert04_U_0.contains) [1, 9, 13] = true := by decide +kernel
private theorem cert04_forward_250 : cert04_L_250.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9, 13] cert04_L_251 cert04_forward_leaf_250 cert04_forward_251
private theorem cert04_forward_leaf_249 : (cert04_U_0.contains) [1, 9, 11] = true := by decide +kernel
private theorem cert04_forward_249 : cert04_L_249.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9, 11] cert04_L_250 cert04_forward_leaf_249 cert04_forward_250
private theorem cert04_forward_leaf_248 : (cert04_U_0.contains) [1, 11, 19] = true := by decide +kernel
private theorem cert04_forward_248 : cert04_L_248.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 11, 19] cert04_L_249 cert04_forward_leaf_248 cert04_forward_249
private theorem cert04_forward_leaf_247 : (cert04_U_0.contains) [1, 11, 15] = true := by decide +kernel
private theorem cert04_forward_247 : cert04_L_247.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 11, 15] cert04_L_248 cert04_forward_leaf_247 cert04_forward_248
private theorem cert04_forward_leaf_246 : (cert04_U_0.contains) [1, 13, 19] = true := by decide +kernel
private theorem cert04_forward_246 : cert04_L_246.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 13, 19] cert04_L_247 cert04_forward_leaf_246 cert04_forward_247
private theorem cert04_forward_leaf_245 : (cert04_U_0.contains) [1, 13, 15] = true := by decide +kernel
private theorem cert04_forward_245 : cert04_L_245.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 13, 15] cert04_L_246 cert04_forward_leaf_245 cert04_forward_246
private theorem cert04_forward_leaf_244 : (cert04_U_0.contains) [1, 16, 17, 19] = true := by decide +kernel
private theorem cert04_forward_244 : cert04_L_244.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 16, 17, 19] cert04_L_245 cert04_forward_leaf_244 cert04_forward_245
private theorem cert04_forward_leaf_243 : (cert04_U_0.contains) [1, 16, 17, 18] = true := by decide +kernel
private theorem cert04_forward_243 : cert04_L_243.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 16, 17, 18] cert04_L_244 cert04_forward_leaf_243 cert04_forward_244
private theorem cert04_forward_leaf_242 : (cert04_U_0.contains) [1, 16, 18, 19] = true := by decide +kernel
private theorem cert04_forward_242 : cert04_L_242.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 16, 18, 19] cert04_L_243 cert04_forward_leaf_242 cert04_forward_243
private theorem cert04_forward_leaf_241 : (cert04_U_0.contains) [1, 16, 19] = true := by decide +kernel
private theorem cert04_forward_241 : cert04_L_241.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 16, 19] cert04_L_242 cert04_forward_leaf_241 cert04_forward_242
private theorem cert04_forward_leaf_240 : (cert04_U_0.contains) [1, 16, 18] = true := by decide +kernel
private theorem cert04_forward_240 : cert04_L_240.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 16, 18] cert04_L_241 cert04_forward_leaf_240 cert04_forward_241
private theorem cert04_forward_leaf_239 : (cert04_U_0.contains) [1, 16, 17] = true := by decide +kernel
private theorem cert04_forward_239 : cert04_L_239.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 16, 17] cert04_L_240 cert04_forward_leaf_239 cert04_forward_240
private theorem cert04_forward_leaf_238 : (cert04_U_0.contains) [1, 17, 19] = true := by decide +kernel
private theorem cert04_forward_238 : cert04_L_238.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 17, 19] cert04_L_239 cert04_forward_leaf_238 cert04_forward_239
private theorem cert04_forward_leaf_237 : (cert04_U_0.contains) [1, 17, 18] = true := by decide +kernel
private theorem cert04_forward_237 : cert04_L_237.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 17, 18] cert04_L_238 cert04_forward_leaf_237 cert04_forward_238
private theorem cert04_forward_leaf_236 : (cert04_U_0.contains) [1, 18, 19] = true := by decide +kernel
private theorem cert04_forward_236 : cert04_L_236.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 18, 19] cert04_L_237 cert04_forward_leaf_236 cert04_forward_237
private theorem cert04_forward_leaf_235 : (cert04_U_0.contains) [1, 19] = true := by decide +kernel
private theorem cert04_forward_235 : cert04_L_235.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 19] cert04_L_236 cert04_forward_leaf_235 cert04_forward_236
private theorem cert04_forward_leaf_234 : (cert04_U_0.contains) [1, 18] = true := by decide +kernel
private theorem cert04_forward_234 : cert04_L_234.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 18] cert04_L_235 cert04_forward_leaf_234 cert04_forward_235
private theorem cert04_forward_leaf_233 : (cert04_U_0.contains) [1, 17] = true := by decide +kernel
private theorem cert04_forward_233 : cert04_L_233.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 17] cert04_L_234 cert04_forward_leaf_233 cert04_forward_234
private theorem cert04_forward_leaf_232 : (cert04_U_0.contains) [1, 16] = true := by decide +kernel
private theorem cert04_forward_232 : cert04_L_232.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 16] cert04_L_233 cert04_forward_leaf_232 cert04_forward_233
private theorem cert04_forward_leaf_231 : (cert04_U_0.contains) [1, 15] = true := by decide +kernel
private theorem cert04_forward_231 : cert04_L_231.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 15] cert04_L_232 cert04_forward_leaf_231 cert04_forward_232
private theorem cert04_forward_leaf_230 : (cert04_U_0.contains) [1, 13] = true := by decide +kernel
private theorem cert04_forward_230 : cert04_L_230.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 13] cert04_L_231 cert04_forward_leaf_230 cert04_forward_231
private theorem cert04_forward_leaf_229 : (cert04_U_0.contains) [1, 11] = true := by decide +kernel
private theorem cert04_forward_229 : cert04_L_229.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 11] cert04_L_230 cert04_forward_leaf_229 cert04_forward_230
private theorem cert04_forward_leaf_228 : (cert04_U_0.contains) [1, 9] = true := by decide +kernel
private theorem cert04_forward_228 : cert04_L_228.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 9] cert04_L_229 cert04_forward_leaf_228 cert04_forward_229
private theorem cert04_forward_leaf_227 : (cert04_U_0.contains) [1, 7] = true := by decide +kernel
private theorem cert04_forward_227 : cert04_L_227.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 7] cert04_L_228 cert04_forward_leaf_227 cert04_forward_228
private theorem cert04_forward_leaf_226 : (cert04_U_0.contains) [1, 5] = true := by decide +kernel
private theorem cert04_forward_226 : cert04_L_226.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 5] cert04_L_227 cert04_forward_leaf_226 cert04_forward_227
private theorem cert04_forward_leaf_225 : (cert04_U_0.contains) [1, 3] = true := by decide +kernel
private theorem cert04_forward_225 : cert04_L_225.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1, 3] cert04_L_226 cert04_forward_leaf_225 cert04_forward_226
private theorem cert04_forward_leaf_224 : (cert04_U_0.contains) [2, 3, 7, 18] = true := by decide +kernel
private theorem cert04_forward_224 : cert04_L_224.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 7, 18] cert04_L_225 cert04_forward_leaf_224 cert04_forward_225
private theorem cert04_forward_leaf_223 : (cert04_U_0.contains) [2, 3, 7, 15] = true := by decide +kernel
private theorem cert04_forward_223 : cert04_L_223.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 7, 15] cert04_L_224 cert04_forward_leaf_223 cert04_forward_224
private theorem cert04_forward_leaf_222 : (cert04_U_0.contains) [2, 3, 11, 19] = true := by decide +kernel
private theorem cert04_forward_222 : cert04_L_222.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 11, 19] cert04_L_223 cert04_forward_leaf_222 cert04_forward_223
private theorem cert04_forward_leaf_221 : (cert04_U_0.contains) [2, 3, 11, 15] = true := by decide +kernel
private theorem cert04_forward_221 : cert04_L_221.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 11, 15] cert04_L_222 cert04_forward_leaf_221 cert04_forward_222
private theorem cert04_forward_leaf_220 : (cert04_U_0.contains) [2, 3, 17, 19] = true := by decide +kernel
private theorem cert04_forward_220 : cert04_L_220.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 17, 19] cert04_L_221 cert04_forward_leaf_220 cert04_forward_221
private theorem cert04_forward_leaf_219 : (cert04_U_0.contains) [2, 3, 17, 18] = true := by decide +kernel
private theorem cert04_forward_219 : cert04_L_219.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 17, 18] cert04_L_220 cert04_forward_leaf_219 cert04_forward_220
private theorem cert04_forward_leaf_218 : (cert04_U_0.contains) [2, 3, 19] = true := by decide +kernel
private theorem cert04_forward_218 : cert04_L_218.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 19] cert04_L_219 cert04_forward_leaf_218 cert04_forward_219
private theorem cert04_forward_leaf_217 : (cert04_U_0.contains) [2, 3, 18] = true := by decide +kernel
private theorem cert04_forward_217 : cert04_L_217.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 18] cert04_L_218 cert04_forward_leaf_217 cert04_forward_218
private theorem cert04_forward_leaf_216 : (cert04_U_0.contains) [2, 3, 17] = true := by decide +kernel
private theorem cert04_forward_216 : cert04_L_216.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 17] cert04_L_217 cert04_forward_leaf_216 cert04_forward_217
private theorem cert04_forward_leaf_215 : (cert04_U_0.contains) [2, 3, 15] = true := by decide +kernel
private theorem cert04_forward_215 : cert04_L_215.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 15] cert04_L_216 cert04_forward_leaf_215 cert04_forward_216
private theorem cert04_forward_leaf_214 : (cert04_U_0.contains) [2, 3, 11] = true := by decide +kernel
private theorem cert04_forward_214 : cert04_L_214.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 11] cert04_L_215 cert04_forward_leaf_214 cert04_forward_215
private theorem cert04_forward_leaf_213 : (cert04_U_0.contains) [2, 3, 7] = true := by decide +kernel
private theorem cert04_forward_213 : cert04_L_213.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3, 7] cert04_L_214 cert04_forward_leaf_213 cert04_forward_214
private theorem cert04_forward_leaf_212 : (cert04_U_0.contains) [2, 6, 7, 18] = true := by decide +kernel
private theorem cert04_forward_212 : cert04_L_212.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 7, 18] cert04_L_213 cert04_forward_leaf_212 cert04_forward_213
private theorem cert04_forward_leaf_211 : (cert04_U_0.contains) [2, 6, 7, 15] = true := by decide +kernel
private theorem cert04_forward_211 : cert04_L_211.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 7, 15] cert04_L_212 cert04_forward_leaf_211 cert04_forward_212
private theorem cert04_forward_leaf_210 : (cert04_U_0.contains) [2, 6, 14, 19] = true := by decide +kernel
private theorem cert04_forward_210 : cert04_L_210.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 14, 19] cert04_L_211 cert04_forward_leaf_210 cert04_forward_211
private theorem cert04_forward_leaf_209 : (cert04_U_0.contains) [2, 6, 14, 15] = true := by decide +kernel
private theorem cert04_forward_209 : cert04_L_209.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 14, 15] cert04_L_210 cert04_forward_leaf_209 cert04_forward_210
private theorem cert04_forward_leaf_208 : (cert04_U_0.contains) [2, 6, 18, 19] = true := by decide +kernel
private theorem cert04_forward_208 : cert04_L_208.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 18, 19] cert04_L_209 cert04_forward_leaf_208 cert04_forward_209
private theorem cert04_forward_leaf_207 : (cert04_U_0.contains) [2, 6, 19] = true := by decide +kernel
private theorem cert04_forward_207 : cert04_L_207.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 19] cert04_L_208 cert04_forward_leaf_207 cert04_forward_208
private theorem cert04_forward_leaf_206 : (cert04_U_0.contains) [2, 6, 18] = true := by decide +kernel
private theorem cert04_forward_206 : cert04_L_206.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 18] cert04_L_207 cert04_forward_leaf_206 cert04_forward_207
private theorem cert04_forward_leaf_205 : (cert04_U_0.contains) [2, 6, 15] = true := by decide +kernel
private theorem cert04_forward_205 : cert04_L_205.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 15] cert04_L_206 cert04_forward_leaf_205 cert04_forward_206
private theorem cert04_forward_leaf_204 : (cert04_U_0.contains) [2, 6, 14] = true := by decide +kernel
private theorem cert04_forward_204 : cert04_L_204.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 14] cert04_L_205 cert04_forward_leaf_204 cert04_forward_205
private theorem cert04_forward_leaf_203 : (cert04_U_0.contains) [2, 6, 7] = true := by decide +kernel
private theorem cert04_forward_203 : cert04_L_203.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6, 7] cert04_L_204 cert04_forward_leaf_203 cert04_forward_204
private theorem cert04_forward_leaf_202 : (cert04_U_0.contains) [2, 7, 18] = true := by decide +kernel
private theorem cert04_forward_202 : cert04_L_202.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 7, 18] cert04_L_203 cert04_forward_leaf_202 cert04_forward_203
private theorem cert04_forward_leaf_201 : (cert04_U_0.contains) [2, 7, 15] = true := by decide +kernel
private theorem cert04_forward_201 : cert04_L_201.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 7, 15] cert04_L_202 cert04_forward_leaf_201 cert04_forward_202
private theorem cert04_forward_leaf_200 : (cert04_U_0.contains) [2, 10, 11, 19] = true := by decide +kernel
private theorem cert04_forward_200 : cert04_L_200.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10, 11, 19] cert04_L_201 cert04_forward_leaf_200 cert04_forward_201
private theorem cert04_forward_leaf_199 : (cert04_U_0.contains) [2, 10, 11, 15] = true := by decide +kernel
private theorem cert04_forward_199 : cert04_L_199.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10, 11, 15] cert04_L_200 cert04_forward_leaf_199 cert04_forward_200
private theorem cert04_forward_leaf_198 : (cert04_U_0.contains) [2, 10, 14, 19] = true := by decide +kernel
private theorem cert04_forward_198 : cert04_L_198.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10, 14, 19] cert04_L_199 cert04_forward_leaf_198 cert04_forward_199
private theorem cert04_forward_leaf_197 : (cert04_U_0.contains) [2, 10, 14, 15] = true := by decide +kernel
private theorem cert04_forward_197 : cert04_L_197.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10, 14, 15] cert04_L_198 cert04_forward_leaf_197 cert04_forward_198
private theorem cert04_forward_leaf_196 : (cert04_U_0.contains) [2, 10, 19] = true := by decide +kernel
private theorem cert04_forward_196 : cert04_L_196.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10, 19] cert04_L_197 cert04_forward_leaf_196 cert04_forward_197
private theorem cert04_forward_leaf_195 : (cert04_U_0.contains) [2, 10, 15] = true := by decide +kernel
private theorem cert04_forward_195 : cert04_L_195.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10, 15] cert04_L_196 cert04_forward_leaf_195 cert04_forward_196
private theorem cert04_forward_leaf_194 : (cert04_U_0.contains) [2, 10, 14] = true := by decide +kernel
private theorem cert04_forward_194 : cert04_L_194.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10, 14] cert04_L_195 cert04_forward_leaf_194 cert04_forward_195
private theorem cert04_forward_leaf_193 : (cert04_U_0.contains) [2, 10, 11] = true := by decide +kernel
private theorem cert04_forward_193 : cert04_L_193.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10, 11] cert04_L_194 cert04_forward_leaf_193 cert04_forward_194
private theorem cert04_forward_leaf_192 : (cert04_U_0.contains) [2, 11, 19] = true := by decide +kernel
private theorem cert04_forward_192 : cert04_L_192.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 11, 19] cert04_L_193 cert04_forward_leaf_192 cert04_forward_193
private theorem cert04_forward_leaf_191 : (cert04_U_0.contains) [2, 11, 15] = true := by decide +kernel
private theorem cert04_forward_191 : cert04_L_191.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 11, 15] cert04_L_192 cert04_forward_leaf_191 cert04_forward_192
private theorem cert04_forward_leaf_190 : (cert04_U_0.contains) [2, 14, 19] = true := by decide +kernel
private theorem cert04_forward_190 : cert04_L_190.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 14, 19] cert04_L_191 cert04_forward_leaf_190 cert04_forward_191
private theorem cert04_forward_leaf_189 : (cert04_U_0.contains) [2, 14, 15] = true := by decide +kernel
private theorem cert04_forward_189 : cert04_L_189.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 14, 15] cert04_L_190 cert04_forward_leaf_189 cert04_forward_190
private theorem cert04_forward_leaf_188 : (cert04_U_0.contains) [2, 17, 18, 19] = true := by decide +kernel
private theorem cert04_forward_188 : cert04_L_188.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 17, 18, 19] cert04_L_189 cert04_forward_leaf_188 cert04_forward_189
private theorem cert04_forward_leaf_187 : (cert04_U_0.contains) [2, 17, 19] = true := by decide +kernel
private theorem cert04_forward_187 : cert04_L_187.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 17, 19] cert04_L_188 cert04_forward_leaf_187 cert04_forward_188
private theorem cert04_forward_leaf_186 : (cert04_U_0.contains) [2, 17, 18] = true := by decide +kernel
private theorem cert04_forward_186 : cert04_L_186.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 17, 18] cert04_L_187 cert04_forward_leaf_186 cert04_forward_187
private theorem cert04_forward_leaf_185 : (cert04_U_0.contains) [2, 18, 19] = true := by decide +kernel
private theorem cert04_forward_185 : cert04_L_185.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 18, 19] cert04_L_186 cert04_forward_leaf_185 cert04_forward_186
private theorem cert04_forward_leaf_184 : (cert04_U_0.contains) [2, 19] = true := by decide +kernel
private theorem cert04_forward_184 : cert04_L_184.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 19] cert04_L_185 cert04_forward_leaf_184 cert04_forward_185
private theorem cert04_forward_leaf_183 : (cert04_U_0.contains) [2, 18] = true := by decide +kernel
private theorem cert04_forward_183 : cert04_L_183.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 18] cert04_L_184 cert04_forward_leaf_183 cert04_forward_184
private theorem cert04_forward_leaf_182 : (cert04_U_0.contains) [2, 17] = true := by decide +kernel
private theorem cert04_forward_182 : cert04_L_182.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 17] cert04_L_183 cert04_forward_leaf_182 cert04_forward_183
private theorem cert04_forward_leaf_181 : (cert04_U_0.contains) [2, 15] = true := by decide +kernel
private theorem cert04_forward_181 : cert04_L_181.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 15] cert04_L_182 cert04_forward_leaf_181 cert04_forward_182
private theorem cert04_forward_leaf_180 : (cert04_U_0.contains) [2, 14] = true := by decide +kernel
private theorem cert04_forward_180 : cert04_L_180.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 14] cert04_L_181 cert04_forward_leaf_180 cert04_forward_181
private theorem cert04_forward_leaf_179 : (cert04_U_0.contains) [2, 11] = true := by decide +kernel
private theorem cert04_forward_179 : cert04_L_179.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 11] cert04_L_180 cert04_forward_leaf_179 cert04_forward_180
private theorem cert04_forward_leaf_178 : (cert04_U_0.contains) [2, 10] = true := by decide +kernel
private theorem cert04_forward_178 : cert04_L_178.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 10] cert04_L_179 cert04_forward_leaf_178 cert04_forward_179
private theorem cert04_forward_leaf_177 : (cert04_U_0.contains) [2, 7] = true := by decide +kernel
private theorem cert04_forward_177 : cert04_L_177.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 7] cert04_L_178 cert04_forward_leaf_177 cert04_forward_178
private theorem cert04_forward_leaf_176 : (cert04_U_0.contains) [2, 6] = true := by decide +kernel
private theorem cert04_forward_176 : cert04_L_176.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 6] cert04_L_177 cert04_forward_leaf_176 cert04_forward_177
private theorem cert04_forward_leaf_175 : (cert04_U_0.contains) [2, 3] = true := by decide +kernel
private theorem cert04_forward_175 : cert04_L_175.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2, 3] cert04_L_176 cert04_forward_leaf_175 cert04_forward_176
private theorem cert04_forward_leaf_174 : (cert04_U_0.contains) [3, 7, 18] = true := by decide +kernel
private theorem cert04_forward_174 : cert04_L_174.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 7, 18] cert04_L_175 cert04_forward_leaf_174 cert04_forward_175
private theorem cert04_forward_leaf_173 : (cert04_U_0.contains) [3, 7, 15] = true := by decide +kernel
private theorem cert04_forward_173 : cert04_L_173.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 7, 15] cert04_L_174 cert04_forward_leaf_173 cert04_forward_174
private theorem cert04_forward_leaf_172 : (cert04_U_0.contains) [3, 11, 19] = true := by decide +kernel
private theorem cert04_forward_172 : cert04_L_172.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 11, 19] cert04_L_173 cert04_forward_leaf_172 cert04_forward_173
private theorem cert04_forward_leaf_171 : (cert04_U_0.contains) [3, 11, 15] = true := by decide +kernel
private theorem cert04_forward_171 : cert04_L_171.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 11, 15] cert04_L_172 cert04_forward_leaf_171 cert04_forward_172
private theorem cert04_forward_leaf_170 : (cert04_U_0.contains) [3, 17, 19] = true := by decide +kernel
private theorem cert04_forward_170 : cert04_L_170.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 17, 19] cert04_L_171 cert04_forward_leaf_170 cert04_forward_171
private theorem cert04_forward_leaf_169 : (cert04_U_0.contains) [3, 17, 18] = true := by decide +kernel
private theorem cert04_forward_169 : cert04_L_169.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 17, 18] cert04_L_170 cert04_forward_leaf_169 cert04_forward_170
private theorem cert04_forward_leaf_168 : (cert04_U_0.contains) [3, 19] = true := by decide +kernel
private theorem cert04_forward_168 : cert04_L_168.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 19] cert04_L_169 cert04_forward_leaf_168 cert04_forward_169
private theorem cert04_forward_leaf_167 : (cert04_U_0.contains) [3, 18] = true := by decide +kernel
private theorem cert04_forward_167 : cert04_L_167.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 18] cert04_L_168 cert04_forward_leaf_167 cert04_forward_168
private theorem cert04_forward_leaf_166 : (cert04_U_0.contains) [3, 17] = true := by decide +kernel
private theorem cert04_forward_166 : cert04_L_166.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 17] cert04_L_167 cert04_forward_leaf_166 cert04_forward_167
private theorem cert04_forward_leaf_165 : (cert04_U_0.contains) [3, 15] = true := by decide +kernel
private theorem cert04_forward_165 : cert04_L_165.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 15] cert04_L_166 cert04_forward_leaf_165 cert04_forward_166
private theorem cert04_forward_leaf_164 : (cert04_U_0.contains) [3, 11] = true := by decide +kernel
private theorem cert04_forward_164 : cert04_L_164.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 11] cert04_L_165 cert04_forward_leaf_164 cert04_forward_165
private theorem cert04_forward_leaf_163 : (cert04_U_0.contains) [3, 7] = true := by decide +kernel
private theorem cert04_forward_163 : cert04_L_163.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3, 7] cert04_L_164 cert04_forward_leaf_163 cert04_forward_164
private theorem cert04_forward_leaf_162 : (cert04_U_0.contains) [4, 5, 7, 18] = true := by decide +kernel
private theorem cert04_forward_162 : cert04_L_162.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 7, 18] cert04_L_163 cert04_forward_leaf_162 cert04_forward_163
private theorem cert04_forward_leaf_161 : (cert04_U_0.contains) [4, 5, 7, 15] = true := by decide +kernel
private theorem cert04_forward_161 : cert04_L_161.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 7, 15] cert04_L_162 cert04_forward_leaf_161 cert04_forward_162
private theorem cert04_forward_leaf_160 : (cert04_U_0.contains) [4, 5, 13, 19] = true := by decide +kernel
private theorem cert04_forward_160 : cert04_L_160.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 13, 19] cert04_L_161 cert04_forward_leaf_160 cert04_forward_161
private theorem cert04_forward_leaf_159 : (cert04_U_0.contains) [4, 5, 13, 15] = true := by decide +kernel
private theorem cert04_forward_159 : cert04_L_159.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 13, 15] cert04_L_160 cert04_forward_leaf_159 cert04_forward_160
private theorem cert04_forward_leaf_158 : (cert04_U_0.contains) [4, 5, 18, 19] = true := by decide +kernel
private theorem cert04_forward_158 : cert04_L_158.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 18, 19] cert04_L_159 cert04_forward_leaf_158 cert04_forward_159
private theorem cert04_forward_leaf_157 : (cert04_U_0.contains) [4, 5, 19] = true := by decide +kernel
private theorem cert04_forward_157 : cert04_L_157.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 19] cert04_L_158 cert04_forward_leaf_157 cert04_forward_158
private theorem cert04_forward_leaf_156 : (cert04_U_0.contains) [4, 5, 18] = true := by decide +kernel
private theorem cert04_forward_156 : cert04_L_156.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 18] cert04_L_157 cert04_forward_leaf_156 cert04_forward_157
private theorem cert04_forward_leaf_155 : (cert04_U_0.contains) [4, 5, 15] = true := by decide +kernel
private theorem cert04_forward_155 : cert04_L_155.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 15] cert04_L_156 cert04_forward_leaf_155 cert04_forward_156
private theorem cert04_forward_leaf_154 : (cert04_U_0.contains) [4, 5, 13] = true := by decide +kernel
private theorem cert04_forward_154 : cert04_L_154.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 13] cert04_L_155 cert04_forward_leaf_154 cert04_forward_155
private theorem cert04_forward_leaf_153 : (cert04_U_0.contains) [4, 5, 7] = true := by decide +kernel
private theorem cert04_forward_153 : cert04_L_153.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5, 7] cert04_L_154 cert04_forward_leaf_153 cert04_forward_154
private theorem cert04_forward_leaf_152 : (cert04_U_0.contains) [4, 6, 7, 18] = true := by decide +kernel
private theorem cert04_forward_152 : cert04_L_152.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 7, 18] cert04_L_153 cert04_forward_leaf_152 cert04_forward_153
private theorem cert04_forward_leaf_151 : (cert04_U_0.contains) [4, 6, 7, 15] = true := by decide +kernel
private theorem cert04_forward_151 : cert04_L_151.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 7, 15] cert04_L_152 cert04_forward_leaf_151 cert04_forward_152
private theorem cert04_forward_leaf_150 : (cert04_U_0.contains) [4, 6, 14, 19] = true := by decide +kernel
private theorem cert04_forward_150 : cert04_L_150.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 14, 19] cert04_L_151 cert04_forward_leaf_150 cert04_forward_151
private theorem cert04_forward_leaf_149 : (cert04_U_0.contains) [4, 6, 14, 15] = true := by decide +kernel
private theorem cert04_forward_149 : cert04_L_149.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 14, 15] cert04_L_150 cert04_forward_leaf_149 cert04_forward_150
private theorem cert04_forward_leaf_148 : (cert04_U_0.contains) [4, 6, 18, 19] = true := by decide +kernel
private theorem cert04_forward_148 : cert04_L_148.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 18, 19] cert04_L_149 cert04_forward_leaf_148 cert04_forward_149
private theorem cert04_forward_leaf_147 : (cert04_U_0.contains) [4, 6, 19] = true := by decide +kernel
private theorem cert04_forward_147 : cert04_L_147.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 19] cert04_L_148 cert04_forward_leaf_147 cert04_forward_148
private theorem cert04_forward_leaf_146 : (cert04_U_0.contains) [4, 6, 18] = true := by decide +kernel
private theorem cert04_forward_146 : cert04_L_146.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 18] cert04_L_147 cert04_forward_leaf_146 cert04_forward_147
private theorem cert04_forward_leaf_145 : (cert04_U_0.contains) [4, 6, 15] = true := by decide +kernel
private theorem cert04_forward_145 : cert04_L_145.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 15] cert04_L_146 cert04_forward_leaf_145 cert04_forward_146
private theorem cert04_forward_leaf_144 : (cert04_U_0.contains) [4, 6, 14] = true := by decide +kernel
private theorem cert04_forward_144 : cert04_L_144.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 14] cert04_L_145 cert04_forward_leaf_144 cert04_forward_145
private theorem cert04_forward_leaf_143 : (cert04_U_0.contains) [4, 6, 7] = true := by decide +kernel
private theorem cert04_forward_143 : cert04_L_143.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6, 7] cert04_L_144 cert04_forward_leaf_143 cert04_forward_144
private theorem cert04_forward_leaf_142 : (cert04_U_0.contains) [4, 7, 18] = true := by decide +kernel
private theorem cert04_forward_142 : cert04_L_142.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 7, 18] cert04_L_143 cert04_forward_leaf_142 cert04_forward_143
private theorem cert04_forward_leaf_141 : (cert04_U_0.contains) [4, 7, 15] = true := by decide +kernel
private theorem cert04_forward_141 : cert04_L_141.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 7, 15] cert04_L_142 cert04_forward_leaf_141 cert04_forward_142
private theorem cert04_forward_leaf_140 : (cert04_U_0.contains) [4, 12, 13, 19] = true := by decide +kernel
private theorem cert04_forward_140 : cert04_L_140.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12, 13, 19] cert04_L_141 cert04_forward_leaf_140 cert04_forward_141
private theorem cert04_forward_leaf_139 : (cert04_U_0.contains) [4, 12, 13, 15] = true := by decide +kernel
private theorem cert04_forward_139 : cert04_L_139.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12, 13, 15] cert04_L_140 cert04_forward_leaf_139 cert04_forward_140
private theorem cert04_forward_leaf_138 : (cert04_U_0.contains) [4, 12, 14, 19] = true := by decide +kernel
private theorem cert04_forward_138 : cert04_L_138.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12, 14, 19] cert04_L_139 cert04_forward_leaf_138 cert04_forward_139
private theorem cert04_forward_leaf_137 : (cert04_U_0.contains) [4, 12, 14, 15] = true := by decide +kernel
private theorem cert04_forward_137 : cert04_L_137.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12, 14, 15] cert04_L_138 cert04_forward_leaf_137 cert04_forward_138
private theorem cert04_forward_leaf_136 : (cert04_U_0.contains) [4, 12, 19] = true := by decide +kernel
private theorem cert04_forward_136 : cert04_L_136.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12, 19] cert04_L_137 cert04_forward_leaf_136 cert04_forward_137
private theorem cert04_forward_leaf_135 : (cert04_U_0.contains) [4, 12, 15] = true := by decide +kernel
private theorem cert04_forward_135 : cert04_L_135.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12, 15] cert04_L_136 cert04_forward_leaf_135 cert04_forward_136
private theorem cert04_forward_leaf_134 : (cert04_U_0.contains) [4, 12, 14] = true := by decide +kernel
private theorem cert04_forward_134 : cert04_L_134.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12, 14] cert04_L_135 cert04_forward_leaf_134 cert04_forward_135
private theorem cert04_forward_leaf_133 : (cert04_U_0.contains) [4, 12, 13] = true := by decide +kernel
private theorem cert04_forward_133 : cert04_L_133.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12, 13] cert04_L_134 cert04_forward_leaf_133 cert04_forward_134
private theorem cert04_forward_leaf_132 : (cert04_U_0.contains) [4, 13, 19] = true := by decide +kernel
private theorem cert04_forward_132 : cert04_L_132.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 13, 19] cert04_L_133 cert04_forward_leaf_132 cert04_forward_133
private theorem cert04_forward_leaf_131 : (cert04_U_0.contains) [4, 13, 15] = true := by decide +kernel
private theorem cert04_forward_131 : cert04_L_131.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 13, 15] cert04_L_132 cert04_forward_leaf_131 cert04_forward_132
private theorem cert04_forward_leaf_130 : (cert04_U_0.contains) [4, 14, 19] = true := by decide +kernel
private theorem cert04_forward_130 : cert04_L_130.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 14, 19] cert04_L_131 cert04_forward_leaf_130 cert04_forward_131
private theorem cert04_forward_leaf_129 : (cert04_U_0.contains) [4, 14, 15] = true := by decide +kernel
private theorem cert04_forward_129 : cert04_L_129.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 14, 15] cert04_L_130 cert04_forward_leaf_129 cert04_forward_130
private theorem cert04_forward_leaf_128 : (cert04_U_0.contains) [4, 18, 19] = true := by decide +kernel
private theorem cert04_forward_128 : cert04_L_128.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 18, 19] cert04_L_129 cert04_forward_leaf_128 cert04_forward_129
private theorem cert04_forward_leaf_127 : (cert04_U_0.contains) [4, 19] = true := by decide +kernel
private theorem cert04_forward_127 : cert04_L_127.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 19] cert04_L_128 cert04_forward_leaf_127 cert04_forward_128
private theorem cert04_forward_leaf_126 : (cert04_U_0.contains) [4, 18] = true := by decide +kernel
private theorem cert04_forward_126 : cert04_L_126.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 18] cert04_L_127 cert04_forward_leaf_126 cert04_forward_127
private theorem cert04_forward_leaf_125 : (cert04_U_0.contains) [4, 15] = true := by decide +kernel
private theorem cert04_forward_125 : cert04_L_125.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 15] cert04_L_126 cert04_forward_leaf_125 cert04_forward_126
private theorem cert04_forward_leaf_124 : (cert04_U_0.contains) [4, 14] = true := by decide +kernel
private theorem cert04_forward_124 : cert04_L_124.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 14] cert04_L_125 cert04_forward_leaf_124 cert04_forward_125
private theorem cert04_forward_leaf_123 : (cert04_U_0.contains) [4, 13] = true := by decide +kernel
private theorem cert04_forward_123 : cert04_L_123.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 13] cert04_L_124 cert04_forward_leaf_123 cert04_forward_124
private theorem cert04_forward_leaf_122 : (cert04_U_0.contains) [4, 12] = true := by decide +kernel
private theorem cert04_forward_122 : cert04_L_122.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 12] cert04_L_123 cert04_forward_leaf_122 cert04_forward_123
private theorem cert04_forward_leaf_121 : (cert04_U_0.contains) [4, 7] = true := by decide +kernel
private theorem cert04_forward_121 : cert04_L_121.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 7] cert04_L_122 cert04_forward_leaf_121 cert04_forward_122
private theorem cert04_forward_leaf_120 : (cert04_U_0.contains) [4, 6] = true := by decide +kernel
private theorem cert04_forward_120 : cert04_L_120.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 6] cert04_L_121 cert04_forward_leaf_120 cert04_forward_121
private theorem cert04_forward_leaf_119 : (cert04_U_0.contains) [4, 5] = true := by decide +kernel
private theorem cert04_forward_119 : cert04_L_119.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4, 5] cert04_L_120 cert04_forward_leaf_119 cert04_forward_120
private theorem cert04_forward_leaf_118 : (cert04_U_0.contains) [5, 7, 18] = true := by decide +kernel
private theorem cert04_forward_118 : cert04_L_118.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 7, 18] cert04_L_119 cert04_forward_leaf_118 cert04_forward_119
private theorem cert04_forward_leaf_117 : (cert04_U_0.contains) [5, 7, 15] = true := by decide +kernel
private theorem cert04_forward_117 : cert04_L_117.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 7, 15] cert04_L_118 cert04_forward_leaf_117 cert04_forward_118
private theorem cert04_forward_leaf_116 : (cert04_U_0.contains) [5, 13, 19] = true := by decide +kernel
private theorem cert04_forward_116 : cert04_L_116.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 13, 19] cert04_L_117 cert04_forward_leaf_116 cert04_forward_117
private theorem cert04_forward_leaf_115 : (cert04_U_0.contains) [5, 13, 15] = true := by decide +kernel
private theorem cert04_forward_115 : cert04_L_115.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 13, 15] cert04_L_116 cert04_forward_leaf_115 cert04_forward_116
private theorem cert04_forward_leaf_114 : (cert04_U_0.contains) [5, 18, 19] = true := by decide +kernel
private theorem cert04_forward_114 : cert04_L_114.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 18, 19] cert04_L_115 cert04_forward_leaf_114 cert04_forward_115
private theorem cert04_forward_leaf_113 : (cert04_U_0.contains) [5, 19] = true := by decide +kernel
private theorem cert04_forward_113 : cert04_L_113.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 19] cert04_L_114 cert04_forward_leaf_113 cert04_forward_114
private theorem cert04_forward_leaf_112 : (cert04_U_0.contains) [5, 18] = true := by decide +kernel
private theorem cert04_forward_112 : cert04_L_112.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 18] cert04_L_113 cert04_forward_leaf_112 cert04_forward_113
private theorem cert04_forward_leaf_111 : (cert04_U_0.contains) [5, 15] = true := by decide +kernel
private theorem cert04_forward_111 : cert04_L_111.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 15] cert04_L_112 cert04_forward_leaf_111 cert04_forward_112
private theorem cert04_forward_leaf_110 : (cert04_U_0.contains) [5, 13] = true := by decide +kernel
private theorem cert04_forward_110 : cert04_L_110.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 13] cert04_L_111 cert04_forward_leaf_110 cert04_forward_111
private theorem cert04_forward_leaf_109 : (cert04_U_0.contains) [5, 7] = true := by decide +kernel
private theorem cert04_forward_109 : cert04_L_109.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5, 7] cert04_L_110 cert04_forward_leaf_109 cert04_forward_110
private theorem cert04_forward_leaf_108 : (cert04_U_0.contains) [6, 7, 18] = true := by decide +kernel
private theorem cert04_forward_108 : cert04_L_108.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 7, 18] cert04_L_109 cert04_forward_leaf_108 cert04_forward_109
private theorem cert04_forward_leaf_107 : (cert04_U_0.contains) [6, 7, 15] = true := by decide +kernel
private theorem cert04_forward_107 : cert04_L_107.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 7, 15] cert04_L_108 cert04_forward_leaf_107 cert04_forward_108
private theorem cert04_forward_leaf_106 : (cert04_U_0.contains) [6, 14, 19] = true := by decide +kernel
private theorem cert04_forward_106 : cert04_L_106.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 14, 19] cert04_L_107 cert04_forward_leaf_106 cert04_forward_107
private theorem cert04_forward_leaf_105 : (cert04_U_0.contains) [6, 14, 15] = true := by decide +kernel
private theorem cert04_forward_105 : cert04_L_105.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 14, 15] cert04_L_106 cert04_forward_leaf_105 cert04_forward_106
private theorem cert04_forward_leaf_104 : (cert04_U_0.contains) [6, 18, 19] = true := by decide +kernel
private theorem cert04_forward_104 : cert04_L_104.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 18, 19] cert04_L_105 cert04_forward_leaf_104 cert04_forward_105
private theorem cert04_forward_leaf_103 : (cert04_U_0.contains) [6, 19] = true := by decide +kernel
private theorem cert04_forward_103 : cert04_L_103.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 19] cert04_L_104 cert04_forward_leaf_103 cert04_forward_104
private theorem cert04_forward_leaf_102 : (cert04_U_0.contains) [6, 18] = true := by decide +kernel
private theorem cert04_forward_102 : cert04_L_102.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 18] cert04_L_103 cert04_forward_leaf_102 cert04_forward_103
private theorem cert04_forward_leaf_101 : (cert04_U_0.contains) [6, 15] = true := by decide +kernel
private theorem cert04_forward_101 : cert04_L_101.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 15] cert04_L_102 cert04_forward_leaf_101 cert04_forward_102
private theorem cert04_forward_leaf_100 : (cert04_U_0.contains) [6, 14] = true := by decide +kernel
private theorem cert04_forward_100 : cert04_L_100.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 14] cert04_L_101 cert04_forward_leaf_100 cert04_forward_101
private theorem cert04_forward_leaf_99 : (cert04_U_0.contains) [6, 7] = true := by decide +kernel
private theorem cert04_forward_99 : cert04_L_99.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6, 7] cert04_L_100 cert04_forward_leaf_99 cert04_forward_100
private theorem cert04_forward_leaf_98 : (cert04_U_0.contains) [7, 18] = true := by decide +kernel
private theorem cert04_forward_98 : cert04_L_98.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [7, 18] cert04_L_99 cert04_forward_leaf_98 cert04_forward_99
private theorem cert04_forward_leaf_97 : (cert04_U_0.contains) [7, 15] = true := by decide +kernel
private theorem cert04_forward_97 : cert04_L_97.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [7, 15] cert04_L_98 cert04_forward_leaf_97 cert04_forward_98
private theorem cert04_forward_leaf_96 : (cert04_U_0.contains) [8, 9, 11, 19] = true := by decide +kernel
private theorem cert04_forward_96 : cert04_L_96.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9, 11, 19] cert04_L_97 cert04_forward_leaf_96 cert04_forward_97
private theorem cert04_forward_leaf_95 : (cert04_U_0.contains) [8, 9, 11, 15] = true := by decide +kernel
private theorem cert04_forward_95 : cert04_L_95.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9, 11, 15] cert04_L_96 cert04_forward_leaf_95 cert04_forward_96
private theorem cert04_forward_leaf_94 : (cert04_U_0.contains) [8, 9, 13, 19] = true := by decide +kernel
private theorem cert04_forward_94 : cert04_L_94.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9, 13, 19] cert04_L_95 cert04_forward_leaf_94 cert04_forward_95
private theorem cert04_forward_leaf_93 : (cert04_U_0.contains) [8, 9, 13, 15] = true := by decide +kernel
private theorem cert04_forward_93 : cert04_L_93.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9, 13, 15] cert04_L_94 cert04_forward_leaf_93 cert04_forward_94
private theorem cert04_forward_leaf_92 : (cert04_U_0.contains) [8, 9, 19] = true := by decide +kernel
private theorem cert04_forward_92 : cert04_L_92.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9, 19] cert04_L_93 cert04_forward_leaf_92 cert04_forward_93
private theorem cert04_forward_leaf_91 : (cert04_U_0.contains) [8, 9, 15] = true := by decide +kernel
private theorem cert04_forward_91 : cert04_L_91.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9, 15] cert04_L_92 cert04_forward_leaf_91 cert04_forward_92
private theorem cert04_forward_leaf_90 : (cert04_U_0.contains) [8, 9, 13] = true := by decide +kernel
private theorem cert04_forward_90 : cert04_L_90.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9, 13] cert04_L_91 cert04_forward_leaf_90 cert04_forward_91
private theorem cert04_forward_leaf_89 : (cert04_U_0.contains) [8, 9, 11] = true := by decide +kernel
private theorem cert04_forward_89 : cert04_L_89.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9, 11] cert04_L_90 cert04_forward_leaf_89 cert04_forward_90
private theorem cert04_forward_leaf_88 : (cert04_U_0.contains) [8, 10, 11, 19] = true := by decide +kernel
private theorem cert04_forward_88 : cert04_L_88.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10, 11, 19] cert04_L_89 cert04_forward_leaf_88 cert04_forward_89
private theorem cert04_forward_leaf_87 : (cert04_U_0.contains) [8, 10, 11, 15] = true := by decide +kernel
private theorem cert04_forward_87 : cert04_L_87.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10, 11, 15] cert04_L_88 cert04_forward_leaf_87 cert04_forward_88
private theorem cert04_forward_leaf_86 : (cert04_U_0.contains) [8, 10, 14, 19] = true := by decide +kernel
private theorem cert04_forward_86 : cert04_L_86.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10, 14, 19] cert04_L_87 cert04_forward_leaf_86 cert04_forward_87
private theorem cert04_forward_leaf_85 : (cert04_U_0.contains) [8, 10, 14, 15] = true := by decide +kernel
private theorem cert04_forward_85 : cert04_L_85.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10, 14, 15] cert04_L_86 cert04_forward_leaf_85 cert04_forward_86
private theorem cert04_forward_leaf_84 : (cert04_U_0.contains) [8, 10, 19] = true := by decide +kernel
private theorem cert04_forward_84 : cert04_L_84.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10, 19] cert04_L_85 cert04_forward_leaf_84 cert04_forward_85
private theorem cert04_forward_leaf_83 : (cert04_U_0.contains) [8, 10, 15] = true := by decide +kernel
private theorem cert04_forward_83 : cert04_L_83.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10, 15] cert04_L_84 cert04_forward_leaf_83 cert04_forward_84
private theorem cert04_forward_leaf_82 : (cert04_U_0.contains) [8, 10, 14] = true := by decide +kernel
private theorem cert04_forward_82 : cert04_L_82.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10, 14] cert04_L_83 cert04_forward_leaf_82 cert04_forward_83
private theorem cert04_forward_leaf_81 : (cert04_U_0.contains) [8, 10, 11] = true := by decide +kernel
private theorem cert04_forward_81 : cert04_L_81.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10, 11] cert04_L_82 cert04_forward_leaf_81 cert04_forward_82
private theorem cert04_forward_leaf_80 : (cert04_U_0.contains) [8, 11, 19] = true := by decide +kernel
private theorem cert04_forward_80 : cert04_L_80.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 11, 19] cert04_L_81 cert04_forward_leaf_80 cert04_forward_81
private theorem cert04_forward_leaf_79 : (cert04_U_0.contains) [8, 11, 15] = true := by decide +kernel
private theorem cert04_forward_79 : cert04_L_79.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 11, 15] cert04_L_80 cert04_forward_leaf_79 cert04_forward_80
private theorem cert04_forward_leaf_78 : (cert04_U_0.contains) [8, 12, 13, 19] = true := by decide +kernel
private theorem cert04_forward_78 : cert04_L_78.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12, 13, 19] cert04_L_79 cert04_forward_leaf_78 cert04_forward_79
private theorem cert04_forward_leaf_77 : (cert04_U_0.contains) [8, 12, 13, 15] = true := by decide +kernel
private theorem cert04_forward_77 : cert04_L_77.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12, 13, 15] cert04_L_78 cert04_forward_leaf_77 cert04_forward_78
private theorem cert04_forward_leaf_76 : (cert04_U_0.contains) [8, 12, 14, 19] = true := by decide +kernel
private theorem cert04_forward_76 : cert04_L_76.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12, 14, 19] cert04_L_77 cert04_forward_leaf_76 cert04_forward_77
private theorem cert04_forward_leaf_75 : (cert04_U_0.contains) [8, 12, 14, 15] = true := by decide +kernel
private theorem cert04_forward_75 : cert04_L_75.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12, 14, 15] cert04_L_76 cert04_forward_leaf_75 cert04_forward_76
private theorem cert04_forward_leaf_74 : (cert04_U_0.contains) [8, 12, 19] = true := by decide +kernel
private theorem cert04_forward_74 : cert04_L_74.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12, 19] cert04_L_75 cert04_forward_leaf_74 cert04_forward_75
private theorem cert04_forward_leaf_73 : (cert04_U_0.contains) [8, 12, 15] = true := by decide +kernel
private theorem cert04_forward_73 : cert04_L_73.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12, 15] cert04_L_74 cert04_forward_leaf_73 cert04_forward_74
private theorem cert04_forward_leaf_72 : (cert04_U_0.contains) [8, 12, 14] = true := by decide +kernel
private theorem cert04_forward_72 : cert04_L_72.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12, 14] cert04_L_73 cert04_forward_leaf_72 cert04_forward_73
private theorem cert04_forward_leaf_71 : (cert04_U_0.contains) [8, 12, 13] = true := by decide +kernel
private theorem cert04_forward_71 : cert04_L_71.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12, 13] cert04_L_72 cert04_forward_leaf_71 cert04_forward_72
private theorem cert04_forward_leaf_70 : (cert04_U_0.contains) [8, 13, 19] = true := by decide +kernel
private theorem cert04_forward_70 : cert04_L_70.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 13, 19] cert04_L_71 cert04_forward_leaf_70 cert04_forward_71
private theorem cert04_forward_leaf_69 : (cert04_U_0.contains) [8, 13, 15] = true := by decide +kernel
private theorem cert04_forward_69 : cert04_L_69.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 13, 15] cert04_L_70 cert04_forward_leaf_69 cert04_forward_70
private theorem cert04_forward_leaf_68 : (cert04_U_0.contains) [8, 14, 19] = true := by decide +kernel
private theorem cert04_forward_68 : cert04_L_68.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 14, 19] cert04_L_69 cert04_forward_leaf_68 cert04_forward_69
private theorem cert04_forward_leaf_67 : (cert04_U_0.contains) [8, 14, 15] = true := by decide +kernel
private theorem cert04_forward_67 : cert04_L_67.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 14, 15] cert04_L_68 cert04_forward_leaf_67 cert04_forward_68
private theorem cert04_forward_leaf_66 : (cert04_U_0.contains) [8, 19] = true := by decide +kernel
private theorem cert04_forward_66 : cert04_L_66.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 19] cert04_L_67 cert04_forward_leaf_66 cert04_forward_67
private theorem cert04_forward_leaf_65 : (cert04_U_0.contains) [8, 15] = true := by decide +kernel
private theorem cert04_forward_65 : cert04_L_65.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 15] cert04_L_66 cert04_forward_leaf_65 cert04_forward_66
private theorem cert04_forward_leaf_64 : (cert04_U_0.contains) [8, 14] = true := by decide +kernel
private theorem cert04_forward_64 : cert04_L_64.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 14] cert04_L_65 cert04_forward_leaf_64 cert04_forward_65
private theorem cert04_forward_leaf_63 : (cert04_U_0.contains) [8, 13] = true := by decide +kernel
private theorem cert04_forward_63 : cert04_L_63.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 13] cert04_L_64 cert04_forward_leaf_63 cert04_forward_64
private theorem cert04_forward_leaf_62 : (cert04_U_0.contains) [8, 12] = true := by decide +kernel
private theorem cert04_forward_62 : cert04_L_62.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 12] cert04_L_63 cert04_forward_leaf_62 cert04_forward_63
private theorem cert04_forward_leaf_61 : (cert04_U_0.contains) [8, 11] = true := by decide +kernel
private theorem cert04_forward_61 : cert04_L_61.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 11] cert04_L_62 cert04_forward_leaf_61 cert04_forward_62
private theorem cert04_forward_leaf_60 : (cert04_U_0.contains) [8, 10] = true := by decide +kernel
private theorem cert04_forward_60 : cert04_L_60.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 10] cert04_L_61 cert04_forward_leaf_60 cert04_forward_61
private theorem cert04_forward_leaf_59 : (cert04_U_0.contains) [8, 9] = true := by decide +kernel
private theorem cert04_forward_59 : cert04_L_59.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8, 9] cert04_L_60 cert04_forward_leaf_59 cert04_forward_60
private theorem cert04_forward_leaf_58 : (cert04_U_0.contains) [9, 11, 19] = true := by decide +kernel
private theorem cert04_forward_58 : cert04_L_58.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9, 11, 19] cert04_L_59 cert04_forward_leaf_58 cert04_forward_59
private theorem cert04_forward_leaf_57 : (cert04_U_0.contains) [9, 11, 15] = true := by decide +kernel
private theorem cert04_forward_57 : cert04_L_57.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9, 11, 15] cert04_L_58 cert04_forward_leaf_57 cert04_forward_58
private theorem cert04_forward_leaf_56 : (cert04_U_0.contains) [9, 13, 19] = true := by decide +kernel
private theorem cert04_forward_56 : cert04_L_56.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9, 13, 19] cert04_L_57 cert04_forward_leaf_56 cert04_forward_57
private theorem cert04_forward_leaf_55 : (cert04_U_0.contains) [9, 13, 15] = true := by decide +kernel
private theorem cert04_forward_55 : cert04_L_55.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9, 13, 15] cert04_L_56 cert04_forward_leaf_55 cert04_forward_56
private theorem cert04_forward_leaf_54 : (cert04_U_0.contains) [9, 19] = true := by decide +kernel
private theorem cert04_forward_54 : cert04_L_54.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9, 19] cert04_L_55 cert04_forward_leaf_54 cert04_forward_55
private theorem cert04_forward_leaf_53 : (cert04_U_0.contains) [9, 15] = true := by decide +kernel
private theorem cert04_forward_53 : cert04_L_53.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9, 15] cert04_L_54 cert04_forward_leaf_53 cert04_forward_54
private theorem cert04_forward_leaf_52 : (cert04_U_0.contains) [9, 13] = true := by decide +kernel
private theorem cert04_forward_52 : cert04_L_52.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9, 13] cert04_L_53 cert04_forward_leaf_52 cert04_forward_53
private theorem cert04_forward_leaf_51 : (cert04_U_0.contains) [9, 11] = true := by decide +kernel
private theorem cert04_forward_51 : cert04_L_51.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9, 11] cert04_L_52 cert04_forward_leaf_51 cert04_forward_52
private theorem cert04_forward_leaf_50 : (cert04_U_0.contains) [10, 11, 19] = true := by decide +kernel
private theorem cert04_forward_50 : cert04_L_50.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10, 11, 19] cert04_L_51 cert04_forward_leaf_50 cert04_forward_51
private theorem cert04_forward_leaf_49 : (cert04_U_0.contains) [10, 11, 15] = true := by decide +kernel
private theorem cert04_forward_49 : cert04_L_49.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10, 11, 15] cert04_L_50 cert04_forward_leaf_49 cert04_forward_50
private theorem cert04_forward_leaf_48 : (cert04_U_0.contains) [10, 14, 19] = true := by decide +kernel
private theorem cert04_forward_48 : cert04_L_48.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10, 14, 19] cert04_L_49 cert04_forward_leaf_48 cert04_forward_49
private theorem cert04_forward_leaf_47 : (cert04_U_0.contains) [10, 14, 15] = true := by decide +kernel
private theorem cert04_forward_47 : cert04_L_47.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10, 14, 15] cert04_L_48 cert04_forward_leaf_47 cert04_forward_48
private theorem cert04_forward_leaf_46 : (cert04_U_0.contains) [10, 19] = true := by decide +kernel
private theorem cert04_forward_46 : cert04_L_46.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10, 19] cert04_L_47 cert04_forward_leaf_46 cert04_forward_47
private theorem cert04_forward_leaf_45 : (cert04_U_0.contains) [10, 15] = true := by decide +kernel
private theorem cert04_forward_45 : cert04_L_45.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10, 15] cert04_L_46 cert04_forward_leaf_45 cert04_forward_46
private theorem cert04_forward_leaf_44 : (cert04_U_0.contains) [10, 14] = true := by decide +kernel
private theorem cert04_forward_44 : cert04_L_44.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10, 14] cert04_L_45 cert04_forward_leaf_44 cert04_forward_45
private theorem cert04_forward_leaf_43 : (cert04_U_0.contains) [10, 11] = true := by decide +kernel
private theorem cert04_forward_43 : cert04_L_43.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10, 11] cert04_L_44 cert04_forward_leaf_43 cert04_forward_44
private theorem cert04_forward_leaf_42 : (cert04_U_0.contains) [11, 19] = true := by decide +kernel
private theorem cert04_forward_42 : cert04_L_42.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [11, 19] cert04_L_43 cert04_forward_leaf_42 cert04_forward_43
private theorem cert04_forward_leaf_41 : (cert04_U_0.contains) [11, 15] = true := by decide +kernel
private theorem cert04_forward_41 : cert04_L_41.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [11, 15] cert04_L_42 cert04_forward_leaf_41 cert04_forward_42
private theorem cert04_forward_leaf_40 : (cert04_U_0.contains) [12, 13, 19] = true := by decide +kernel
private theorem cert04_forward_40 : cert04_L_40.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12, 13, 19] cert04_L_41 cert04_forward_leaf_40 cert04_forward_41
private theorem cert04_forward_leaf_39 : (cert04_U_0.contains) [12, 13, 15] = true := by decide +kernel
private theorem cert04_forward_39 : cert04_L_39.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12, 13, 15] cert04_L_40 cert04_forward_leaf_39 cert04_forward_40
private theorem cert04_forward_leaf_38 : (cert04_U_0.contains) [12, 14, 19] = true := by decide +kernel
private theorem cert04_forward_38 : cert04_L_38.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12, 14, 19] cert04_L_39 cert04_forward_leaf_38 cert04_forward_39
private theorem cert04_forward_leaf_37 : (cert04_U_0.contains) [12, 14, 15] = true := by decide +kernel
private theorem cert04_forward_37 : cert04_L_37.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12, 14, 15] cert04_L_38 cert04_forward_leaf_37 cert04_forward_38
private theorem cert04_forward_leaf_36 : (cert04_U_0.contains) [12, 19] = true := by decide +kernel
private theorem cert04_forward_36 : cert04_L_36.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12, 19] cert04_L_37 cert04_forward_leaf_36 cert04_forward_37
private theorem cert04_forward_leaf_35 : (cert04_U_0.contains) [12, 15] = true := by decide +kernel
private theorem cert04_forward_35 : cert04_L_35.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12, 15] cert04_L_36 cert04_forward_leaf_35 cert04_forward_36
private theorem cert04_forward_leaf_34 : (cert04_U_0.contains) [12, 14] = true := by decide +kernel
private theorem cert04_forward_34 : cert04_L_34.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12, 14] cert04_L_35 cert04_forward_leaf_34 cert04_forward_35
private theorem cert04_forward_leaf_33 : (cert04_U_0.contains) [12, 13] = true := by decide +kernel
private theorem cert04_forward_33 : cert04_L_33.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12, 13] cert04_L_34 cert04_forward_leaf_33 cert04_forward_34
private theorem cert04_forward_leaf_32 : (cert04_U_0.contains) [13, 19] = true := by decide +kernel
private theorem cert04_forward_32 : cert04_L_32.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [13, 19] cert04_L_33 cert04_forward_leaf_32 cert04_forward_33
private theorem cert04_forward_leaf_31 : (cert04_U_0.contains) [13, 15] = true := by decide +kernel
private theorem cert04_forward_31 : cert04_L_31.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [13, 15] cert04_L_32 cert04_forward_leaf_31 cert04_forward_32
private theorem cert04_forward_leaf_30 : (cert04_U_0.contains) [14, 19] = true := by decide +kernel
private theorem cert04_forward_30 : cert04_L_30.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [14, 19] cert04_L_31 cert04_forward_leaf_30 cert04_forward_31
private theorem cert04_forward_leaf_29 : (cert04_U_0.contains) [14, 15] = true := by decide +kernel
private theorem cert04_forward_29 : cert04_L_29.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [14, 15] cert04_L_30 cert04_forward_leaf_29 cert04_forward_30
private theorem cert04_forward_leaf_28 : (cert04_U_0.contains) [16, 17, 19] = true := by decide +kernel
private theorem cert04_forward_28 : cert04_L_28.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [16, 17, 19] cert04_L_29 cert04_forward_leaf_28 cert04_forward_29
private theorem cert04_forward_leaf_27 : (cert04_U_0.contains) [16, 17, 18] = true := by decide +kernel
private theorem cert04_forward_27 : cert04_L_27.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [16, 17, 18] cert04_L_28 cert04_forward_leaf_27 cert04_forward_28
private theorem cert04_forward_leaf_26 : (cert04_U_0.contains) [16, 18, 19] = true := by decide +kernel
private theorem cert04_forward_26 : cert04_L_26.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [16, 18, 19] cert04_L_27 cert04_forward_leaf_26 cert04_forward_27
private theorem cert04_forward_leaf_25 : (cert04_U_0.contains) [16, 19] = true := by decide +kernel
private theorem cert04_forward_25 : cert04_L_25.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [16, 19] cert04_L_26 cert04_forward_leaf_25 cert04_forward_26
private theorem cert04_forward_leaf_24 : (cert04_U_0.contains) [16, 18] = true := by decide +kernel
private theorem cert04_forward_24 : cert04_L_24.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [16, 18] cert04_L_25 cert04_forward_leaf_24 cert04_forward_25
private theorem cert04_forward_leaf_23 : (cert04_U_0.contains) [16, 17] = true := by decide +kernel
private theorem cert04_forward_23 : cert04_L_23.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [16, 17] cert04_L_24 cert04_forward_leaf_23 cert04_forward_24
private theorem cert04_forward_leaf_22 : (cert04_U_0.contains) [17, 18, 19] = true := by decide +kernel
private theorem cert04_forward_22 : cert04_L_22.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [17, 18, 19] cert04_L_23 cert04_forward_leaf_22 cert04_forward_23
private theorem cert04_forward_leaf_21 : (cert04_U_0.contains) [17, 19] = true := by decide +kernel
private theorem cert04_forward_21 : cert04_L_21.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [17, 19] cert04_L_22 cert04_forward_leaf_21 cert04_forward_22
private theorem cert04_forward_leaf_20 : (cert04_U_0.contains) [17, 18] = true := by decide +kernel
private theorem cert04_forward_20 : cert04_L_20.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [17, 18] cert04_L_21 cert04_forward_leaf_20 cert04_forward_21
private theorem cert04_forward_leaf_19 : (cert04_U_0.contains) [18, 19] = true := by decide +kernel
private theorem cert04_forward_19 : cert04_L_19.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [18, 19] cert04_L_20 cert04_forward_leaf_19 cert04_forward_20
private theorem cert04_forward_leaf_18 : (cert04_U_0.contains) [19] = true := by decide +kernel
private theorem cert04_forward_18 : cert04_L_18.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [19] cert04_L_19 cert04_forward_leaf_18 cert04_forward_19
private theorem cert04_forward_leaf_17 : (cert04_U_0.contains) [18] = true := by decide +kernel
private theorem cert04_forward_17 : cert04_L_17.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [18] cert04_L_18 cert04_forward_leaf_17 cert04_forward_18
private theorem cert04_forward_leaf_16 : (cert04_U_0.contains) [17] = true := by decide +kernel
private theorem cert04_forward_16 : cert04_L_16.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [17] cert04_L_17 cert04_forward_leaf_16 cert04_forward_17
private theorem cert04_forward_leaf_15 : (cert04_U_0.contains) [16] = true := by decide +kernel
private theorem cert04_forward_15 : cert04_L_15.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [16] cert04_L_16 cert04_forward_leaf_15 cert04_forward_16
private theorem cert04_forward_leaf_14 : (cert04_U_0.contains) [15] = true := by decide +kernel
private theorem cert04_forward_14 : cert04_L_14.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [15] cert04_L_15 cert04_forward_leaf_14 cert04_forward_15
private theorem cert04_forward_leaf_13 : (cert04_U_0.contains) [14] = true := by decide +kernel
private theorem cert04_forward_13 : cert04_L_13.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [14] cert04_L_14 cert04_forward_leaf_13 cert04_forward_14
private theorem cert04_forward_leaf_12 : (cert04_U_0.contains) [13] = true := by decide +kernel
private theorem cert04_forward_12 : cert04_L_12.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [13] cert04_L_13 cert04_forward_leaf_12 cert04_forward_13
private theorem cert04_forward_leaf_11 : (cert04_U_0.contains) [12] = true := by decide +kernel
private theorem cert04_forward_11 : cert04_L_11.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [12] cert04_L_12 cert04_forward_leaf_11 cert04_forward_12
private theorem cert04_forward_leaf_10 : (cert04_U_0.contains) [11] = true := by decide +kernel
private theorem cert04_forward_10 : cert04_L_10.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [11] cert04_L_11 cert04_forward_leaf_10 cert04_forward_11
private theorem cert04_forward_leaf_9 : (cert04_U_0.contains) [10] = true := by decide +kernel
private theorem cert04_forward_9 : cert04_L_9.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [10] cert04_L_10 cert04_forward_leaf_9 cert04_forward_10
private theorem cert04_forward_leaf_8 : (cert04_U_0.contains) [9] = true := by decide +kernel
private theorem cert04_forward_8 : cert04_L_8.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [9] cert04_L_9 cert04_forward_leaf_8 cert04_forward_9
private theorem cert04_forward_leaf_7 : (cert04_U_0.contains) [8] = true := by decide +kernel
private theorem cert04_forward_7 : cert04_L_7.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [8] cert04_L_8 cert04_forward_leaf_7 cert04_forward_8
private theorem cert04_forward_leaf_6 : (cert04_U_0.contains) [7] = true := by decide +kernel
private theorem cert04_forward_6 : cert04_L_6.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [7] cert04_L_7 cert04_forward_leaf_6 cert04_forward_7
private theorem cert04_forward_leaf_5 : (cert04_U_0.contains) [6] = true := by decide +kernel
private theorem cert04_forward_5 : cert04_L_5.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [6] cert04_L_6 cert04_forward_leaf_5 cert04_forward_6
private theorem cert04_forward_leaf_4 : (cert04_U_0.contains) [5] = true := by decide +kernel
private theorem cert04_forward_4 : cert04_L_4.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [5] cert04_L_5 cert04_forward_leaf_4 cert04_forward_5
private theorem cert04_forward_leaf_3 : (cert04_U_0.contains) [4] = true := by decide +kernel
private theorem cert04_forward_3 : cert04_L_3.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [4] cert04_L_4 cert04_forward_leaf_3 cert04_forward_4
private theorem cert04_forward_leaf_2 : (cert04_U_0.contains) [3] = true := by decide +kernel
private theorem cert04_forward_2 : cert04_L_2.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [3] cert04_L_3 cert04_forward_leaf_2 cert04_forward_3
private theorem cert04_forward_leaf_1 : (cert04_U_0.contains) [2] = true := by decide +kernel
private theorem cert04_forward_1 : cert04_L_1.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [2] cert04_L_2 cert04_forward_leaf_1 cert04_forward_2
private theorem cert04_forward_leaf_0 : (cert04_U_0.contains) [1] = true := by decide +kernel
private theorem cert04_forward_0 : cert04_L_0.all (cert04_U_0.contains) = true :=
  cert04_all_cons (cert04_U_0.contains) [1] cert04_L_1 cert04_forward_leaf_0 cert04_forward_1
private theorem cert04_backward_391 : cert04_U_391.all (cert04_L_0.contains) = true := rfl
private theorem cert04_backward_leaf_390 : (cert04_L_0.contains) [1, 3, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_390 : cert04_U_390.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 7, 15, 19] cert04_U_391 cert04_backward_leaf_390 cert04_backward_391
private theorem cert04_backward_leaf_389 : (cert04_L_0.contains) [1, 3, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_389 : cert04_U_389.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 7, 18, 19] cert04_U_390 cert04_backward_leaf_389 cert04_backward_390
private theorem cert04_backward_leaf_388 : (cert04_L_0.contains) [1, 3, 7, 19] = true := by decide +kernel
private theorem cert04_backward_388 : cert04_U_388.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 7, 19] cert04_U_389 cert04_backward_leaf_388 cert04_backward_389
private theorem cert04_backward_leaf_387 : (cert04_L_0.contains) [1, 3, 7, 18] = true := by decide +kernel
private theorem cert04_backward_387 : cert04_U_387.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 7, 18] cert04_U_388 cert04_backward_leaf_387 cert04_backward_388
private theorem cert04_backward_leaf_386 : (cert04_L_0.contains) [1, 3, 7, 15] = true := by decide +kernel
private theorem cert04_backward_386 : cert04_U_386.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 7, 15] cert04_U_387 cert04_backward_leaf_386 cert04_backward_387
private theorem cert04_backward_leaf_385 : (cert04_L_0.contains) [1, 3, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_385 : cert04_U_385.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 11, 15, 19] cert04_U_386 cert04_backward_leaf_385 cert04_backward_386
private theorem cert04_backward_leaf_384 : (cert04_L_0.contains) [1, 3, 11, 19] = true := by decide +kernel
private theorem cert04_backward_384 : cert04_U_384.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 11, 19] cert04_U_385 cert04_backward_leaf_384 cert04_backward_385
private theorem cert04_backward_leaf_383 : (cert04_L_0.contains) [1, 3, 11, 15] = true := by decide +kernel
private theorem cert04_backward_383 : cert04_U_383.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 11, 15] cert04_U_384 cert04_backward_leaf_383 cert04_backward_384
private theorem cert04_backward_leaf_382 : (cert04_L_0.contains) [1, 3, 15, 19] = true := by decide +kernel
private theorem cert04_backward_382 : cert04_U_382.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 15, 19] cert04_U_383 cert04_backward_leaf_382 cert04_backward_383
private theorem cert04_backward_leaf_381 : (cert04_L_0.contains) [1, 3, 17, 18, 19] = true := by decide +kernel
private theorem cert04_backward_381 : cert04_U_381.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 17, 18, 19] cert04_U_382 cert04_backward_leaf_381 cert04_backward_382
private theorem cert04_backward_leaf_380 : (cert04_L_0.contains) [1, 3, 17, 19] = true := by decide +kernel
private theorem cert04_backward_380 : cert04_U_380.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 17, 19] cert04_U_381 cert04_backward_leaf_380 cert04_backward_381
private theorem cert04_backward_leaf_379 : (cert04_L_0.contains) [1, 3, 17, 18] = true := by decide +kernel
private theorem cert04_backward_379 : cert04_U_379.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 17, 18] cert04_U_380 cert04_backward_leaf_379 cert04_backward_380
private theorem cert04_backward_leaf_378 : (cert04_L_0.contains) [1, 3, 18, 19] = true := by decide +kernel
private theorem cert04_backward_378 : cert04_U_378.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 18, 19] cert04_U_379 cert04_backward_leaf_378 cert04_backward_379
private theorem cert04_backward_leaf_377 : (cert04_L_0.contains) [1, 3, 19] = true := by decide +kernel
private theorem cert04_backward_377 : cert04_U_377.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 19] cert04_U_378 cert04_backward_leaf_377 cert04_backward_378
private theorem cert04_backward_leaf_376 : (cert04_L_0.contains) [1, 3, 18] = true := by decide +kernel
private theorem cert04_backward_376 : cert04_U_376.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 18] cert04_U_377 cert04_backward_leaf_376 cert04_backward_377
private theorem cert04_backward_leaf_375 : (cert04_L_0.contains) [1, 3, 17] = true := by decide +kernel
private theorem cert04_backward_375 : cert04_U_375.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 17] cert04_U_376 cert04_backward_leaf_375 cert04_backward_376
private theorem cert04_backward_leaf_374 : (cert04_L_0.contains) [1, 3, 15] = true := by decide +kernel
private theorem cert04_backward_374 : cert04_U_374.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 15] cert04_U_375 cert04_backward_leaf_374 cert04_backward_375
private theorem cert04_backward_leaf_373 : (cert04_L_0.contains) [1, 3, 11] = true := by decide +kernel
private theorem cert04_backward_373 : cert04_U_373.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 11] cert04_U_374 cert04_backward_leaf_373 cert04_backward_374
private theorem cert04_backward_leaf_372 : (cert04_L_0.contains) [1, 3, 7] = true := by decide +kernel
private theorem cert04_backward_372 : cert04_U_372.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3, 7] cert04_U_373 cert04_backward_leaf_372 cert04_backward_373
private theorem cert04_backward_leaf_371 : (cert04_L_0.contains) [1, 5, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_371 : cert04_U_371.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 7, 15, 19] cert04_U_372 cert04_backward_leaf_371 cert04_backward_372
private theorem cert04_backward_leaf_370 : (cert04_L_0.contains) [1, 5, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_370 : cert04_U_370.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 7, 18, 19] cert04_U_371 cert04_backward_leaf_370 cert04_backward_371
private theorem cert04_backward_leaf_369 : (cert04_L_0.contains) [1, 5, 7, 19] = true := by decide +kernel
private theorem cert04_backward_369 : cert04_U_369.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 7, 19] cert04_U_370 cert04_backward_leaf_369 cert04_backward_370
private theorem cert04_backward_leaf_368 : (cert04_L_0.contains) [1, 5, 7, 18] = true := by decide +kernel
private theorem cert04_backward_368 : cert04_U_368.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 7, 18] cert04_U_369 cert04_backward_leaf_368 cert04_backward_369
private theorem cert04_backward_leaf_367 : (cert04_L_0.contains) [1, 5, 7, 15] = true := by decide +kernel
private theorem cert04_backward_367 : cert04_U_367.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 7, 15] cert04_U_368 cert04_backward_leaf_367 cert04_backward_368
private theorem cert04_backward_leaf_366 : (cert04_L_0.contains) [1, 5, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_366 : cert04_U_366.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 13, 15, 19] cert04_U_367 cert04_backward_leaf_366 cert04_backward_367
private theorem cert04_backward_leaf_365 : (cert04_L_0.contains) [1, 5, 13, 19] = true := by decide +kernel
private theorem cert04_backward_365 : cert04_U_365.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 13, 19] cert04_U_366 cert04_backward_leaf_365 cert04_backward_366
private theorem cert04_backward_leaf_364 : (cert04_L_0.contains) [1, 5, 13, 15] = true := by decide +kernel
private theorem cert04_backward_364 : cert04_U_364.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 13, 15] cert04_U_365 cert04_backward_leaf_364 cert04_backward_365
private theorem cert04_backward_leaf_363 : (cert04_L_0.contains) [1, 5, 15, 19] = true := by decide +kernel
private theorem cert04_backward_363 : cert04_U_363.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 15, 19] cert04_U_364 cert04_backward_leaf_363 cert04_backward_364
private theorem cert04_backward_leaf_362 : (cert04_L_0.contains) [1, 5, 18, 19] = true := by decide +kernel
private theorem cert04_backward_362 : cert04_U_362.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 18, 19] cert04_U_363 cert04_backward_leaf_362 cert04_backward_363
private theorem cert04_backward_leaf_361 : (cert04_L_0.contains) [1, 5, 19] = true := by decide +kernel
private theorem cert04_backward_361 : cert04_U_361.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 19] cert04_U_362 cert04_backward_leaf_361 cert04_backward_362
private theorem cert04_backward_leaf_360 : (cert04_L_0.contains) [1, 5, 18] = true := by decide +kernel
private theorem cert04_backward_360 : cert04_U_360.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 18] cert04_U_361 cert04_backward_leaf_360 cert04_backward_361
private theorem cert04_backward_leaf_359 : (cert04_L_0.contains) [1, 5, 15] = true := by decide +kernel
private theorem cert04_backward_359 : cert04_U_359.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 15] cert04_U_360 cert04_backward_leaf_359 cert04_backward_360
private theorem cert04_backward_leaf_358 : (cert04_L_0.contains) [1, 5, 13] = true := by decide +kernel
private theorem cert04_backward_358 : cert04_U_358.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 13] cert04_U_359 cert04_backward_leaf_358 cert04_backward_359
private theorem cert04_backward_leaf_357 : (cert04_L_0.contains) [1, 5, 7] = true := by decide +kernel
private theorem cert04_backward_357 : cert04_U_357.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5, 7] cert04_U_358 cert04_backward_leaf_357 cert04_backward_358
private theorem cert04_backward_leaf_356 : (cert04_L_0.contains) [1, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_356 : cert04_U_356.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 7, 15, 19] cert04_U_357 cert04_backward_leaf_356 cert04_backward_357
private theorem cert04_backward_leaf_355 : (cert04_L_0.contains) [1, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_355 : cert04_U_355.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 7, 18, 19] cert04_U_356 cert04_backward_leaf_355 cert04_backward_356
private theorem cert04_backward_leaf_354 : (cert04_L_0.contains) [1, 7, 19] = true := by decide +kernel
private theorem cert04_backward_354 : cert04_U_354.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 7, 19] cert04_U_355 cert04_backward_leaf_354 cert04_backward_355
private theorem cert04_backward_leaf_353 : (cert04_L_0.contains) [1, 7, 18] = true := by decide +kernel
private theorem cert04_backward_353 : cert04_U_353.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 7, 18] cert04_U_354 cert04_backward_leaf_353 cert04_backward_354
private theorem cert04_backward_leaf_352 : (cert04_L_0.contains) [1, 7, 15] = true := by decide +kernel
private theorem cert04_backward_352 : cert04_U_352.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 7, 15] cert04_U_353 cert04_backward_leaf_352 cert04_backward_353
private theorem cert04_backward_leaf_351 : (cert04_L_0.contains) [1, 9, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_351 : cert04_U_351.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9, 11, 15, 19] cert04_U_352 cert04_backward_leaf_351 cert04_backward_352
private theorem cert04_backward_leaf_350 : (cert04_L_0.contains) [1, 9, 11, 19] = true := by decide +kernel
private theorem cert04_backward_350 : cert04_U_350.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9, 11, 19] cert04_U_351 cert04_backward_leaf_350 cert04_backward_351
private theorem cert04_backward_leaf_349 : (cert04_L_0.contains) [1, 9, 11, 15] = true := by decide +kernel
private theorem cert04_backward_349 : cert04_U_349.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9, 11, 15] cert04_U_350 cert04_backward_leaf_349 cert04_backward_350
private theorem cert04_backward_leaf_348 : (cert04_L_0.contains) [1, 9, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_348 : cert04_U_348.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9, 13, 15, 19] cert04_U_349 cert04_backward_leaf_348 cert04_backward_349
private theorem cert04_backward_leaf_347 : (cert04_L_0.contains) [1, 9, 13, 19] = true := by decide +kernel
private theorem cert04_backward_347 : cert04_U_347.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9, 13, 19] cert04_U_348 cert04_backward_leaf_347 cert04_backward_348
private theorem cert04_backward_leaf_346 : (cert04_L_0.contains) [1, 9, 13, 15] = true := by decide +kernel
private theorem cert04_backward_346 : cert04_U_346.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9, 13, 15] cert04_U_347 cert04_backward_leaf_346 cert04_backward_347
private theorem cert04_backward_leaf_345 : (cert04_L_0.contains) [1, 9, 15, 19] = true := by decide +kernel
private theorem cert04_backward_345 : cert04_U_345.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9, 15, 19] cert04_U_346 cert04_backward_leaf_345 cert04_backward_346
private theorem cert04_backward_leaf_344 : (cert04_L_0.contains) [1, 9, 19] = true := by decide +kernel
private theorem cert04_backward_344 : cert04_U_344.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9, 19] cert04_U_345 cert04_backward_leaf_344 cert04_backward_345
private theorem cert04_backward_leaf_343 : (cert04_L_0.contains) [1, 9, 15] = true := by decide +kernel
private theorem cert04_backward_343 : cert04_U_343.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9, 15] cert04_U_344 cert04_backward_leaf_343 cert04_backward_344
private theorem cert04_backward_leaf_342 : (cert04_L_0.contains) [1, 9, 13] = true := by decide +kernel
private theorem cert04_backward_342 : cert04_U_342.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9, 13] cert04_U_343 cert04_backward_leaf_342 cert04_backward_343
private theorem cert04_backward_leaf_341 : (cert04_L_0.contains) [1, 9, 11] = true := by decide +kernel
private theorem cert04_backward_341 : cert04_U_341.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9, 11] cert04_U_342 cert04_backward_leaf_341 cert04_backward_342
private theorem cert04_backward_leaf_340 : (cert04_L_0.contains) [1, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_340 : cert04_U_340.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 11, 15, 19] cert04_U_341 cert04_backward_leaf_340 cert04_backward_341
private theorem cert04_backward_leaf_339 : (cert04_L_0.contains) [1, 11, 19] = true := by decide +kernel
private theorem cert04_backward_339 : cert04_U_339.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 11, 19] cert04_U_340 cert04_backward_leaf_339 cert04_backward_340
private theorem cert04_backward_leaf_338 : (cert04_L_0.contains) [1, 11, 15] = true := by decide +kernel
private theorem cert04_backward_338 : cert04_U_338.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 11, 15] cert04_U_339 cert04_backward_leaf_338 cert04_backward_339
private theorem cert04_backward_leaf_337 : (cert04_L_0.contains) [1, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_337 : cert04_U_337.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 13, 15, 19] cert04_U_338 cert04_backward_leaf_337 cert04_backward_338
private theorem cert04_backward_leaf_336 : (cert04_L_0.contains) [1, 13, 19] = true := by decide +kernel
private theorem cert04_backward_336 : cert04_U_336.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 13, 19] cert04_U_337 cert04_backward_leaf_336 cert04_backward_337
private theorem cert04_backward_leaf_335 : (cert04_L_0.contains) [1, 13, 15] = true := by decide +kernel
private theorem cert04_backward_335 : cert04_U_335.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 13, 15] cert04_U_336 cert04_backward_leaf_335 cert04_backward_336
private theorem cert04_backward_leaf_334 : (cert04_L_0.contains) [1, 15, 19] = true := by decide +kernel
private theorem cert04_backward_334 : cert04_U_334.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 15, 19] cert04_U_335 cert04_backward_leaf_334 cert04_backward_335
private theorem cert04_backward_leaf_333 : (cert04_L_0.contains) [1, 16, 17, 18, 19] = true := by decide +kernel
private theorem cert04_backward_333 : cert04_U_333.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 16, 17, 18, 19] cert04_U_334 cert04_backward_leaf_333 cert04_backward_334
private theorem cert04_backward_leaf_332 : (cert04_L_0.contains) [1, 16, 17, 19] = true := by decide +kernel
private theorem cert04_backward_332 : cert04_U_332.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 16, 17, 19] cert04_U_333 cert04_backward_leaf_332 cert04_backward_333
private theorem cert04_backward_leaf_331 : (cert04_L_0.contains) [1, 16, 17, 18] = true := by decide +kernel
private theorem cert04_backward_331 : cert04_U_331.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 16, 17, 18] cert04_U_332 cert04_backward_leaf_331 cert04_backward_332
private theorem cert04_backward_leaf_330 : (cert04_L_0.contains) [1, 16, 18, 19] = true := by decide +kernel
private theorem cert04_backward_330 : cert04_U_330.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 16, 18, 19] cert04_U_331 cert04_backward_leaf_330 cert04_backward_331
private theorem cert04_backward_leaf_329 : (cert04_L_0.contains) [1, 16, 19] = true := by decide +kernel
private theorem cert04_backward_329 : cert04_U_329.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 16, 19] cert04_U_330 cert04_backward_leaf_329 cert04_backward_330
private theorem cert04_backward_leaf_328 : (cert04_L_0.contains) [1, 16, 18] = true := by decide +kernel
private theorem cert04_backward_328 : cert04_U_328.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 16, 18] cert04_U_329 cert04_backward_leaf_328 cert04_backward_329
private theorem cert04_backward_leaf_327 : (cert04_L_0.contains) [1, 16, 17] = true := by decide +kernel
private theorem cert04_backward_327 : cert04_U_327.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 16, 17] cert04_U_328 cert04_backward_leaf_327 cert04_backward_328
private theorem cert04_backward_leaf_326 : (cert04_L_0.contains) [1, 17, 18, 19] = true := by decide +kernel
private theorem cert04_backward_326 : cert04_U_326.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 17, 18, 19] cert04_U_327 cert04_backward_leaf_326 cert04_backward_327
private theorem cert04_backward_leaf_325 : (cert04_L_0.contains) [1, 17, 19] = true := by decide +kernel
private theorem cert04_backward_325 : cert04_U_325.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 17, 19] cert04_U_326 cert04_backward_leaf_325 cert04_backward_326
private theorem cert04_backward_leaf_324 : (cert04_L_0.contains) [1, 17, 18] = true := by decide +kernel
private theorem cert04_backward_324 : cert04_U_324.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 17, 18] cert04_U_325 cert04_backward_leaf_324 cert04_backward_325
private theorem cert04_backward_leaf_323 : (cert04_L_0.contains) [1, 18, 19] = true := by decide +kernel
private theorem cert04_backward_323 : cert04_U_323.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 18, 19] cert04_U_324 cert04_backward_leaf_323 cert04_backward_324
private theorem cert04_backward_leaf_322 : (cert04_L_0.contains) [1, 19] = true := by decide +kernel
private theorem cert04_backward_322 : cert04_U_322.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 19] cert04_U_323 cert04_backward_leaf_322 cert04_backward_323
private theorem cert04_backward_leaf_321 : (cert04_L_0.contains) [1, 18] = true := by decide +kernel
private theorem cert04_backward_321 : cert04_U_321.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 18] cert04_U_322 cert04_backward_leaf_321 cert04_backward_322
private theorem cert04_backward_leaf_320 : (cert04_L_0.contains) [1, 17] = true := by decide +kernel
private theorem cert04_backward_320 : cert04_U_320.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 17] cert04_U_321 cert04_backward_leaf_320 cert04_backward_321
private theorem cert04_backward_leaf_319 : (cert04_L_0.contains) [1, 16] = true := by decide +kernel
private theorem cert04_backward_319 : cert04_U_319.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 16] cert04_U_320 cert04_backward_leaf_319 cert04_backward_320
private theorem cert04_backward_leaf_318 : (cert04_L_0.contains) [1, 15] = true := by decide +kernel
private theorem cert04_backward_318 : cert04_U_318.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 15] cert04_U_319 cert04_backward_leaf_318 cert04_backward_319
private theorem cert04_backward_leaf_317 : (cert04_L_0.contains) [1, 13] = true := by decide +kernel
private theorem cert04_backward_317 : cert04_U_317.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 13] cert04_U_318 cert04_backward_leaf_317 cert04_backward_318
private theorem cert04_backward_leaf_316 : (cert04_L_0.contains) [1, 11] = true := by decide +kernel
private theorem cert04_backward_316 : cert04_U_316.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 11] cert04_U_317 cert04_backward_leaf_316 cert04_backward_317
private theorem cert04_backward_leaf_315 : (cert04_L_0.contains) [1, 9] = true := by decide +kernel
private theorem cert04_backward_315 : cert04_U_315.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 9] cert04_U_316 cert04_backward_leaf_315 cert04_backward_316
private theorem cert04_backward_leaf_314 : (cert04_L_0.contains) [1, 7] = true := by decide +kernel
private theorem cert04_backward_314 : cert04_U_314.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 7] cert04_U_315 cert04_backward_leaf_314 cert04_backward_315
private theorem cert04_backward_leaf_313 : (cert04_L_0.contains) [1, 5] = true := by decide +kernel
private theorem cert04_backward_313 : cert04_U_313.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 5] cert04_U_314 cert04_backward_leaf_313 cert04_backward_314
private theorem cert04_backward_leaf_312 : (cert04_L_0.contains) [1, 3] = true := by decide +kernel
private theorem cert04_backward_312 : cert04_U_312.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1, 3] cert04_U_313 cert04_backward_leaf_312 cert04_backward_313
private theorem cert04_backward_leaf_311 : (cert04_L_0.contains) [2, 3, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_311 : cert04_U_311.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 7, 15, 19] cert04_U_312 cert04_backward_leaf_311 cert04_backward_312
private theorem cert04_backward_leaf_310 : (cert04_L_0.contains) [2, 3, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_310 : cert04_U_310.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 7, 18, 19] cert04_U_311 cert04_backward_leaf_310 cert04_backward_311
private theorem cert04_backward_leaf_309 : (cert04_L_0.contains) [2, 3, 7, 19] = true := by decide +kernel
private theorem cert04_backward_309 : cert04_U_309.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 7, 19] cert04_U_310 cert04_backward_leaf_309 cert04_backward_310
private theorem cert04_backward_leaf_308 : (cert04_L_0.contains) [2, 3, 7, 18] = true := by decide +kernel
private theorem cert04_backward_308 : cert04_U_308.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 7, 18] cert04_U_309 cert04_backward_leaf_308 cert04_backward_309
private theorem cert04_backward_leaf_307 : (cert04_L_0.contains) [2, 3, 7, 15] = true := by decide +kernel
private theorem cert04_backward_307 : cert04_U_307.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 7, 15] cert04_U_308 cert04_backward_leaf_307 cert04_backward_308
private theorem cert04_backward_leaf_306 : (cert04_L_0.contains) [2, 3, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_306 : cert04_U_306.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 11, 15, 19] cert04_U_307 cert04_backward_leaf_306 cert04_backward_307
private theorem cert04_backward_leaf_305 : (cert04_L_0.contains) [2, 3, 11, 19] = true := by decide +kernel
private theorem cert04_backward_305 : cert04_U_305.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 11, 19] cert04_U_306 cert04_backward_leaf_305 cert04_backward_306
private theorem cert04_backward_leaf_304 : (cert04_L_0.contains) [2, 3, 11, 15] = true := by decide +kernel
private theorem cert04_backward_304 : cert04_U_304.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 11, 15] cert04_U_305 cert04_backward_leaf_304 cert04_backward_305
private theorem cert04_backward_leaf_303 : (cert04_L_0.contains) [2, 3, 15, 19] = true := by decide +kernel
private theorem cert04_backward_303 : cert04_U_303.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 15, 19] cert04_U_304 cert04_backward_leaf_303 cert04_backward_304
private theorem cert04_backward_leaf_302 : (cert04_L_0.contains) [2, 3, 17, 18, 19] = true := by decide +kernel
private theorem cert04_backward_302 : cert04_U_302.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 17, 18, 19] cert04_U_303 cert04_backward_leaf_302 cert04_backward_303
private theorem cert04_backward_leaf_301 : (cert04_L_0.contains) [2, 3, 17, 19] = true := by decide +kernel
private theorem cert04_backward_301 : cert04_U_301.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 17, 19] cert04_U_302 cert04_backward_leaf_301 cert04_backward_302
private theorem cert04_backward_leaf_300 : (cert04_L_0.contains) [2, 3, 17, 18] = true := by decide +kernel
private theorem cert04_backward_300 : cert04_U_300.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 17, 18] cert04_U_301 cert04_backward_leaf_300 cert04_backward_301
private theorem cert04_backward_leaf_299 : (cert04_L_0.contains) [2, 3, 18, 19] = true := by decide +kernel
private theorem cert04_backward_299 : cert04_U_299.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 18, 19] cert04_U_300 cert04_backward_leaf_299 cert04_backward_300
private theorem cert04_backward_leaf_298 : (cert04_L_0.contains) [2, 3, 19] = true := by decide +kernel
private theorem cert04_backward_298 : cert04_U_298.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 19] cert04_U_299 cert04_backward_leaf_298 cert04_backward_299
private theorem cert04_backward_leaf_297 : (cert04_L_0.contains) [2, 3, 18] = true := by decide +kernel
private theorem cert04_backward_297 : cert04_U_297.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 18] cert04_U_298 cert04_backward_leaf_297 cert04_backward_298
private theorem cert04_backward_leaf_296 : (cert04_L_0.contains) [2, 3, 17] = true := by decide +kernel
private theorem cert04_backward_296 : cert04_U_296.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 17] cert04_U_297 cert04_backward_leaf_296 cert04_backward_297
private theorem cert04_backward_leaf_295 : (cert04_L_0.contains) [2, 3, 15] = true := by decide +kernel
private theorem cert04_backward_295 : cert04_U_295.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 15] cert04_U_296 cert04_backward_leaf_295 cert04_backward_296
private theorem cert04_backward_leaf_294 : (cert04_L_0.contains) [2, 3, 11] = true := by decide +kernel
private theorem cert04_backward_294 : cert04_U_294.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 11] cert04_U_295 cert04_backward_leaf_294 cert04_backward_295
private theorem cert04_backward_leaf_293 : (cert04_L_0.contains) [2, 3, 7] = true := by decide +kernel
private theorem cert04_backward_293 : cert04_U_293.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3, 7] cert04_U_294 cert04_backward_leaf_293 cert04_backward_294
private theorem cert04_backward_leaf_292 : (cert04_L_0.contains) [2, 6, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_292 : cert04_U_292.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 7, 15, 19] cert04_U_293 cert04_backward_leaf_292 cert04_backward_293
private theorem cert04_backward_leaf_291 : (cert04_L_0.contains) [2, 6, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_291 : cert04_U_291.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 7, 18, 19] cert04_U_292 cert04_backward_leaf_291 cert04_backward_292
private theorem cert04_backward_leaf_290 : (cert04_L_0.contains) [2, 6, 7, 19] = true := by decide +kernel
private theorem cert04_backward_290 : cert04_U_290.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 7, 19] cert04_U_291 cert04_backward_leaf_290 cert04_backward_291
private theorem cert04_backward_leaf_289 : (cert04_L_0.contains) [2, 6, 7, 18] = true := by decide +kernel
private theorem cert04_backward_289 : cert04_U_289.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 7, 18] cert04_U_290 cert04_backward_leaf_289 cert04_backward_290
private theorem cert04_backward_leaf_288 : (cert04_L_0.contains) [2, 6, 7, 15] = true := by decide +kernel
private theorem cert04_backward_288 : cert04_U_288.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 7, 15] cert04_U_289 cert04_backward_leaf_288 cert04_backward_289
private theorem cert04_backward_leaf_287 : (cert04_L_0.contains) [2, 6, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_287 : cert04_U_287.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 14, 15, 19] cert04_U_288 cert04_backward_leaf_287 cert04_backward_288
private theorem cert04_backward_leaf_286 : (cert04_L_0.contains) [2, 6, 14, 19] = true := by decide +kernel
private theorem cert04_backward_286 : cert04_U_286.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 14, 19] cert04_U_287 cert04_backward_leaf_286 cert04_backward_287
private theorem cert04_backward_leaf_285 : (cert04_L_0.contains) [2, 6, 14, 15] = true := by decide +kernel
private theorem cert04_backward_285 : cert04_U_285.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 14, 15] cert04_U_286 cert04_backward_leaf_285 cert04_backward_286
private theorem cert04_backward_leaf_284 : (cert04_L_0.contains) [2, 6, 15, 19] = true := by decide +kernel
private theorem cert04_backward_284 : cert04_U_284.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 15, 19] cert04_U_285 cert04_backward_leaf_284 cert04_backward_285
private theorem cert04_backward_leaf_283 : (cert04_L_0.contains) [2, 6, 18, 19] = true := by decide +kernel
private theorem cert04_backward_283 : cert04_U_283.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 18, 19] cert04_U_284 cert04_backward_leaf_283 cert04_backward_284
private theorem cert04_backward_leaf_282 : (cert04_L_0.contains) [2, 6, 19] = true := by decide +kernel
private theorem cert04_backward_282 : cert04_U_282.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 19] cert04_U_283 cert04_backward_leaf_282 cert04_backward_283
private theorem cert04_backward_leaf_281 : (cert04_L_0.contains) [2, 6, 18] = true := by decide +kernel
private theorem cert04_backward_281 : cert04_U_281.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 18] cert04_U_282 cert04_backward_leaf_281 cert04_backward_282
private theorem cert04_backward_leaf_280 : (cert04_L_0.contains) [2, 6, 15] = true := by decide +kernel
private theorem cert04_backward_280 : cert04_U_280.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 15] cert04_U_281 cert04_backward_leaf_280 cert04_backward_281
private theorem cert04_backward_leaf_279 : (cert04_L_0.contains) [2, 6, 14] = true := by decide +kernel
private theorem cert04_backward_279 : cert04_U_279.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 14] cert04_U_280 cert04_backward_leaf_279 cert04_backward_280
private theorem cert04_backward_leaf_278 : (cert04_L_0.contains) [2, 6, 7] = true := by decide +kernel
private theorem cert04_backward_278 : cert04_U_278.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6, 7] cert04_U_279 cert04_backward_leaf_278 cert04_backward_279
private theorem cert04_backward_leaf_277 : (cert04_L_0.contains) [2, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_277 : cert04_U_277.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 7, 15, 19] cert04_U_278 cert04_backward_leaf_277 cert04_backward_278
private theorem cert04_backward_leaf_276 : (cert04_L_0.contains) [2, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_276 : cert04_U_276.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 7, 18, 19] cert04_U_277 cert04_backward_leaf_276 cert04_backward_277
private theorem cert04_backward_leaf_275 : (cert04_L_0.contains) [2, 7, 19] = true := by decide +kernel
private theorem cert04_backward_275 : cert04_U_275.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 7, 19] cert04_U_276 cert04_backward_leaf_275 cert04_backward_276
private theorem cert04_backward_leaf_274 : (cert04_L_0.contains) [2, 7, 18] = true := by decide +kernel
private theorem cert04_backward_274 : cert04_U_274.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 7, 18] cert04_U_275 cert04_backward_leaf_274 cert04_backward_275
private theorem cert04_backward_leaf_273 : (cert04_L_0.contains) [2, 7, 15] = true := by decide +kernel
private theorem cert04_backward_273 : cert04_U_273.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 7, 15] cert04_U_274 cert04_backward_leaf_273 cert04_backward_274
private theorem cert04_backward_leaf_272 : (cert04_L_0.contains) [2, 10, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_272 : cert04_U_272.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10, 11, 15, 19] cert04_U_273 cert04_backward_leaf_272 cert04_backward_273
private theorem cert04_backward_leaf_271 : (cert04_L_0.contains) [2, 10, 11, 19] = true := by decide +kernel
private theorem cert04_backward_271 : cert04_U_271.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10, 11, 19] cert04_U_272 cert04_backward_leaf_271 cert04_backward_272
private theorem cert04_backward_leaf_270 : (cert04_L_0.contains) [2, 10, 11, 15] = true := by decide +kernel
private theorem cert04_backward_270 : cert04_U_270.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10, 11, 15] cert04_U_271 cert04_backward_leaf_270 cert04_backward_271
private theorem cert04_backward_leaf_269 : (cert04_L_0.contains) [2, 10, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_269 : cert04_U_269.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10, 14, 15, 19] cert04_U_270 cert04_backward_leaf_269 cert04_backward_270
private theorem cert04_backward_leaf_268 : (cert04_L_0.contains) [2, 10, 14, 19] = true := by decide +kernel
private theorem cert04_backward_268 : cert04_U_268.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10, 14, 19] cert04_U_269 cert04_backward_leaf_268 cert04_backward_269
private theorem cert04_backward_leaf_267 : (cert04_L_0.contains) [2, 10, 14, 15] = true := by decide +kernel
private theorem cert04_backward_267 : cert04_U_267.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10, 14, 15] cert04_U_268 cert04_backward_leaf_267 cert04_backward_268
private theorem cert04_backward_leaf_266 : (cert04_L_0.contains) [2, 10, 15, 19] = true := by decide +kernel
private theorem cert04_backward_266 : cert04_U_266.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10, 15, 19] cert04_U_267 cert04_backward_leaf_266 cert04_backward_267
private theorem cert04_backward_leaf_265 : (cert04_L_0.contains) [2, 10, 19] = true := by decide +kernel
private theorem cert04_backward_265 : cert04_U_265.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10, 19] cert04_U_266 cert04_backward_leaf_265 cert04_backward_266
private theorem cert04_backward_leaf_264 : (cert04_L_0.contains) [2, 10, 15] = true := by decide +kernel
private theorem cert04_backward_264 : cert04_U_264.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10, 15] cert04_U_265 cert04_backward_leaf_264 cert04_backward_265
private theorem cert04_backward_leaf_263 : (cert04_L_0.contains) [2, 10, 14] = true := by decide +kernel
private theorem cert04_backward_263 : cert04_U_263.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10, 14] cert04_U_264 cert04_backward_leaf_263 cert04_backward_264
private theorem cert04_backward_leaf_262 : (cert04_L_0.contains) [2, 10, 11] = true := by decide +kernel
private theorem cert04_backward_262 : cert04_U_262.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10, 11] cert04_U_263 cert04_backward_leaf_262 cert04_backward_263
private theorem cert04_backward_leaf_261 : (cert04_L_0.contains) [2, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_261 : cert04_U_261.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 11, 15, 19] cert04_U_262 cert04_backward_leaf_261 cert04_backward_262
private theorem cert04_backward_leaf_260 : (cert04_L_0.contains) [2, 11, 19] = true := by decide +kernel
private theorem cert04_backward_260 : cert04_U_260.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 11, 19] cert04_U_261 cert04_backward_leaf_260 cert04_backward_261
private theorem cert04_backward_leaf_259 : (cert04_L_0.contains) [2, 11, 15] = true := by decide +kernel
private theorem cert04_backward_259 : cert04_U_259.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 11, 15] cert04_U_260 cert04_backward_leaf_259 cert04_backward_260
private theorem cert04_backward_leaf_258 : (cert04_L_0.contains) [2, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_258 : cert04_U_258.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 14, 15, 19] cert04_U_259 cert04_backward_leaf_258 cert04_backward_259
private theorem cert04_backward_leaf_257 : (cert04_L_0.contains) [2, 14, 19] = true := by decide +kernel
private theorem cert04_backward_257 : cert04_U_257.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 14, 19] cert04_U_258 cert04_backward_leaf_257 cert04_backward_258
private theorem cert04_backward_leaf_256 : (cert04_L_0.contains) [2, 14, 15] = true := by decide +kernel
private theorem cert04_backward_256 : cert04_U_256.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 14, 15] cert04_U_257 cert04_backward_leaf_256 cert04_backward_257
private theorem cert04_backward_leaf_255 : (cert04_L_0.contains) [2, 15, 19] = true := by decide +kernel
private theorem cert04_backward_255 : cert04_U_255.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 15, 19] cert04_U_256 cert04_backward_leaf_255 cert04_backward_256
private theorem cert04_backward_leaf_254 : (cert04_L_0.contains) [2, 17, 18, 19] = true := by decide +kernel
private theorem cert04_backward_254 : cert04_U_254.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 17, 18, 19] cert04_U_255 cert04_backward_leaf_254 cert04_backward_255
private theorem cert04_backward_leaf_253 : (cert04_L_0.contains) [2, 17, 19] = true := by decide +kernel
private theorem cert04_backward_253 : cert04_U_253.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 17, 19] cert04_U_254 cert04_backward_leaf_253 cert04_backward_254
private theorem cert04_backward_leaf_252 : (cert04_L_0.contains) [2, 17, 18] = true := by decide +kernel
private theorem cert04_backward_252 : cert04_U_252.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 17, 18] cert04_U_253 cert04_backward_leaf_252 cert04_backward_253
private theorem cert04_backward_leaf_251 : (cert04_L_0.contains) [2, 18, 19] = true := by decide +kernel
private theorem cert04_backward_251 : cert04_U_251.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 18, 19] cert04_U_252 cert04_backward_leaf_251 cert04_backward_252
private theorem cert04_backward_leaf_250 : (cert04_L_0.contains) [2, 19] = true := by decide +kernel
private theorem cert04_backward_250 : cert04_U_250.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 19] cert04_U_251 cert04_backward_leaf_250 cert04_backward_251
private theorem cert04_backward_leaf_249 : (cert04_L_0.contains) [2, 18] = true := by decide +kernel
private theorem cert04_backward_249 : cert04_U_249.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 18] cert04_U_250 cert04_backward_leaf_249 cert04_backward_250
private theorem cert04_backward_leaf_248 : (cert04_L_0.contains) [2, 17] = true := by decide +kernel
private theorem cert04_backward_248 : cert04_U_248.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 17] cert04_U_249 cert04_backward_leaf_248 cert04_backward_249
private theorem cert04_backward_leaf_247 : (cert04_L_0.contains) [2, 15] = true := by decide +kernel
private theorem cert04_backward_247 : cert04_U_247.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 15] cert04_U_248 cert04_backward_leaf_247 cert04_backward_248
private theorem cert04_backward_leaf_246 : (cert04_L_0.contains) [2, 14] = true := by decide +kernel
private theorem cert04_backward_246 : cert04_U_246.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 14] cert04_U_247 cert04_backward_leaf_246 cert04_backward_247
private theorem cert04_backward_leaf_245 : (cert04_L_0.contains) [2, 11] = true := by decide +kernel
private theorem cert04_backward_245 : cert04_U_245.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 11] cert04_U_246 cert04_backward_leaf_245 cert04_backward_246
private theorem cert04_backward_leaf_244 : (cert04_L_0.contains) [2, 10] = true := by decide +kernel
private theorem cert04_backward_244 : cert04_U_244.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 10] cert04_U_245 cert04_backward_leaf_244 cert04_backward_245
private theorem cert04_backward_leaf_243 : (cert04_L_0.contains) [2, 7] = true := by decide +kernel
private theorem cert04_backward_243 : cert04_U_243.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 7] cert04_U_244 cert04_backward_leaf_243 cert04_backward_244
private theorem cert04_backward_leaf_242 : (cert04_L_0.contains) [2, 6] = true := by decide +kernel
private theorem cert04_backward_242 : cert04_U_242.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 6] cert04_U_243 cert04_backward_leaf_242 cert04_backward_243
private theorem cert04_backward_leaf_241 : (cert04_L_0.contains) [2, 3] = true := by decide +kernel
private theorem cert04_backward_241 : cert04_U_241.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2, 3] cert04_U_242 cert04_backward_leaf_241 cert04_backward_242
private theorem cert04_backward_leaf_240 : (cert04_L_0.contains) [3, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_240 : cert04_U_240.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 7, 15, 19] cert04_U_241 cert04_backward_leaf_240 cert04_backward_241
private theorem cert04_backward_leaf_239 : (cert04_L_0.contains) [3, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_239 : cert04_U_239.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 7, 18, 19] cert04_U_240 cert04_backward_leaf_239 cert04_backward_240
private theorem cert04_backward_leaf_238 : (cert04_L_0.contains) [3, 7, 19] = true := by decide +kernel
private theorem cert04_backward_238 : cert04_U_238.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 7, 19] cert04_U_239 cert04_backward_leaf_238 cert04_backward_239
private theorem cert04_backward_leaf_237 : (cert04_L_0.contains) [3, 7, 18] = true := by decide +kernel
private theorem cert04_backward_237 : cert04_U_237.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 7, 18] cert04_U_238 cert04_backward_leaf_237 cert04_backward_238
private theorem cert04_backward_leaf_236 : (cert04_L_0.contains) [3, 7, 15] = true := by decide +kernel
private theorem cert04_backward_236 : cert04_U_236.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 7, 15] cert04_U_237 cert04_backward_leaf_236 cert04_backward_237
private theorem cert04_backward_leaf_235 : (cert04_L_0.contains) [3, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_235 : cert04_U_235.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 11, 15, 19] cert04_U_236 cert04_backward_leaf_235 cert04_backward_236
private theorem cert04_backward_leaf_234 : (cert04_L_0.contains) [3, 11, 19] = true := by decide +kernel
private theorem cert04_backward_234 : cert04_U_234.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 11, 19] cert04_U_235 cert04_backward_leaf_234 cert04_backward_235
private theorem cert04_backward_leaf_233 : (cert04_L_0.contains) [3, 11, 15] = true := by decide +kernel
private theorem cert04_backward_233 : cert04_U_233.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 11, 15] cert04_U_234 cert04_backward_leaf_233 cert04_backward_234
private theorem cert04_backward_leaf_232 : (cert04_L_0.contains) [3, 15, 19] = true := by decide +kernel
private theorem cert04_backward_232 : cert04_U_232.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 15, 19] cert04_U_233 cert04_backward_leaf_232 cert04_backward_233
private theorem cert04_backward_leaf_231 : (cert04_L_0.contains) [3, 17, 18, 19] = true := by decide +kernel
private theorem cert04_backward_231 : cert04_U_231.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 17, 18, 19] cert04_U_232 cert04_backward_leaf_231 cert04_backward_232
private theorem cert04_backward_leaf_230 : (cert04_L_0.contains) [3, 17, 19] = true := by decide +kernel
private theorem cert04_backward_230 : cert04_U_230.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 17, 19] cert04_U_231 cert04_backward_leaf_230 cert04_backward_231
private theorem cert04_backward_leaf_229 : (cert04_L_0.contains) [3, 17, 18] = true := by decide +kernel
private theorem cert04_backward_229 : cert04_U_229.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 17, 18] cert04_U_230 cert04_backward_leaf_229 cert04_backward_230
private theorem cert04_backward_leaf_228 : (cert04_L_0.contains) [3, 18, 19] = true := by decide +kernel
private theorem cert04_backward_228 : cert04_U_228.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 18, 19] cert04_U_229 cert04_backward_leaf_228 cert04_backward_229
private theorem cert04_backward_leaf_227 : (cert04_L_0.contains) [3, 19] = true := by decide +kernel
private theorem cert04_backward_227 : cert04_U_227.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 19] cert04_U_228 cert04_backward_leaf_227 cert04_backward_228
private theorem cert04_backward_leaf_226 : (cert04_L_0.contains) [3, 18] = true := by decide +kernel
private theorem cert04_backward_226 : cert04_U_226.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 18] cert04_U_227 cert04_backward_leaf_226 cert04_backward_227
private theorem cert04_backward_leaf_225 : (cert04_L_0.contains) [3, 17] = true := by decide +kernel
private theorem cert04_backward_225 : cert04_U_225.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 17] cert04_U_226 cert04_backward_leaf_225 cert04_backward_226
private theorem cert04_backward_leaf_224 : (cert04_L_0.contains) [3, 15] = true := by decide +kernel
private theorem cert04_backward_224 : cert04_U_224.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 15] cert04_U_225 cert04_backward_leaf_224 cert04_backward_225
private theorem cert04_backward_leaf_223 : (cert04_L_0.contains) [3, 11] = true := by decide +kernel
private theorem cert04_backward_223 : cert04_U_223.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 11] cert04_U_224 cert04_backward_leaf_223 cert04_backward_224
private theorem cert04_backward_leaf_222 : (cert04_L_0.contains) [3, 7] = true := by decide +kernel
private theorem cert04_backward_222 : cert04_U_222.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3, 7] cert04_U_223 cert04_backward_leaf_222 cert04_backward_223
private theorem cert04_backward_leaf_221 : (cert04_L_0.contains) [4, 5, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_221 : cert04_U_221.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 7, 15, 19] cert04_U_222 cert04_backward_leaf_221 cert04_backward_222
private theorem cert04_backward_leaf_220 : (cert04_L_0.contains) [4, 5, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_220 : cert04_U_220.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 7, 18, 19] cert04_U_221 cert04_backward_leaf_220 cert04_backward_221
private theorem cert04_backward_leaf_219 : (cert04_L_0.contains) [4, 5, 7, 19] = true := by decide +kernel
private theorem cert04_backward_219 : cert04_U_219.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 7, 19] cert04_U_220 cert04_backward_leaf_219 cert04_backward_220
private theorem cert04_backward_leaf_218 : (cert04_L_0.contains) [4, 5, 7, 18] = true := by decide +kernel
private theorem cert04_backward_218 : cert04_U_218.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 7, 18] cert04_U_219 cert04_backward_leaf_218 cert04_backward_219
private theorem cert04_backward_leaf_217 : (cert04_L_0.contains) [4, 5, 7, 15] = true := by decide +kernel
private theorem cert04_backward_217 : cert04_U_217.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 7, 15] cert04_U_218 cert04_backward_leaf_217 cert04_backward_218
private theorem cert04_backward_leaf_216 : (cert04_L_0.contains) [4, 5, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_216 : cert04_U_216.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 13, 15, 19] cert04_U_217 cert04_backward_leaf_216 cert04_backward_217
private theorem cert04_backward_leaf_215 : (cert04_L_0.contains) [4, 5, 13, 19] = true := by decide +kernel
private theorem cert04_backward_215 : cert04_U_215.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 13, 19] cert04_U_216 cert04_backward_leaf_215 cert04_backward_216
private theorem cert04_backward_leaf_214 : (cert04_L_0.contains) [4, 5, 13, 15] = true := by decide +kernel
private theorem cert04_backward_214 : cert04_U_214.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 13, 15] cert04_U_215 cert04_backward_leaf_214 cert04_backward_215
private theorem cert04_backward_leaf_213 : (cert04_L_0.contains) [4, 5, 15, 19] = true := by decide +kernel
private theorem cert04_backward_213 : cert04_U_213.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 15, 19] cert04_U_214 cert04_backward_leaf_213 cert04_backward_214
private theorem cert04_backward_leaf_212 : (cert04_L_0.contains) [4, 5, 18, 19] = true := by decide +kernel
private theorem cert04_backward_212 : cert04_U_212.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 18, 19] cert04_U_213 cert04_backward_leaf_212 cert04_backward_213
private theorem cert04_backward_leaf_211 : (cert04_L_0.contains) [4, 5, 19] = true := by decide +kernel
private theorem cert04_backward_211 : cert04_U_211.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 19] cert04_U_212 cert04_backward_leaf_211 cert04_backward_212
private theorem cert04_backward_leaf_210 : (cert04_L_0.contains) [4, 5, 18] = true := by decide +kernel
private theorem cert04_backward_210 : cert04_U_210.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 18] cert04_U_211 cert04_backward_leaf_210 cert04_backward_211
private theorem cert04_backward_leaf_209 : (cert04_L_0.contains) [4, 5, 15] = true := by decide +kernel
private theorem cert04_backward_209 : cert04_U_209.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 15] cert04_U_210 cert04_backward_leaf_209 cert04_backward_210
private theorem cert04_backward_leaf_208 : (cert04_L_0.contains) [4, 5, 13] = true := by decide +kernel
private theorem cert04_backward_208 : cert04_U_208.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 13] cert04_U_209 cert04_backward_leaf_208 cert04_backward_209
private theorem cert04_backward_leaf_207 : (cert04_L_0.contains) [4, 5, 7] = true := by decide +kernel
private theorem cert04_backward_207 : cert04_U_207.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5, 7] cert04_U_208 cert04_backward_leaf_207 cert04_backward_208
private theorem cert04_backward_leaf_206 : (cert04_L_0.contains) [4, 6, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_206 : cert04_U_206.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 7, 15, 19] cert04_U_207 cert04_backward_leaf_206 cert04_backward_207
private theorem cert04_backward_leaf_205 : (cert04_L_0.contains) [4, 6, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_205 : cert04_U_205.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 7, 18, 19] cert04_U_206 cert04_backward_leaf_205 cert04_backward_206
private theorem cert04_backward_leaf_204 : (cert04_L_0.contains) [4, 6, 7, 19] = true := by decide +kernel
private theorem cert04_backward_204 : cert04_U_204.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 7, 19] cert04_U_205 cert04_backward_leaf_204 cert04_backward_205
private theorem cert04_backward_leaf_203 : (cert04_L_0.contains) [4, 6, 7, 18] = true := by decide +kernel
private theorem cert04_backward_203 : cert04_U_203.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 7, 18] cert04_U_204 cert04_backward_leaf_203 cert04_backward_204
private theorem cert04_backward_leaf_202 : (cert04_L_0.contains) [4, 6, 7, 15] = true := by decide +kernel
private theorem cert04_backward_202 : cert04_U_202.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 7, 15] cert04_U_203 cert04_backward_leaf_202 cert04_backward_203
private theorem cert04_backward_leaf_201 : (cert04_L_0.contains) [4, 6, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_201 : cert04_U_201.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 14, 15, 19] cert04_U_202 cert04_backward_leaf_201 cert04_backward_202
private theorem cert04_backward_leaf_200 : (cert04_L_0.contains) [4, 6, 14, 19] = true := by decide +kernel
private theorem cert04_backward_200 : cert04_U_200.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 14, 19] cert04_U_201 cert04_backward_leaf_200 cert04_backward_201
private theorem cert04_backward_leaf_199 : (cert04_L_0.contains) [4, 6, 14, 15] = true := by decide +kernel
private theorem cert04_backward_199 : cert04_U_199.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 14, 15] cert04_U_200 cert04_backward_leaf_199 cert04_backward_200
private theorem cert04_backward_leaf_198 : (cert04_L_0.contains) [4, 6, 15, 19] = true := by decide +kernel
private theorem cert04_backward_198 : cert04_U_198.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 15, 19] cert04_U_199 cert04_backward_leaf_198 cert04_backward_199
private theorem cert04_backward_leaf_197 : (cert04_L_0.contains) [4, 6, 18, 19] = true := by decide +kernel
private theorem cert04_backward_197 : cert04_U_197.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 18, 19] cert04_U_198 cert04_backward_leaf_197 cert04_backward_198
private theorem cert04_backward_leaf_196 : (cert04_L_0.contains) [4, 6, 19] = true := by decide +kernel
private theorem cert04_backward_196 : cert04_U_196.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 19] cert04_U_197 cert04_backward_leaf_196 cert04_backward_197
private theorem cert04_backward_leaf_195 : (cert04_L_0.contains) [4, 6, 18] = true := by decide +kernel
private theorem cert04_backward_195 : cert04_U_195.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 18] cert04_U_196 cert04_backward_leaf_195 cert04_backward_196
private theorem cert04_backward_leaf_194 : (cert04_L_0.contains) [4, 6, 15] = true := by decide +kernel
private theorem cert04_backward_194 : cert04_U_194.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 15] cert04_U_195 cert04_backward_leaf_194 cert04_backward_195
private theorem cert04_backward_leaf_193 : (cert04_L_0.contains) [4, 6, 14] = true := by decide +kernel
private theorem cert04_backward_193 : cert04_U_193.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 14] cert04_U_194 cert04_backward_leaf_193 cert04_backward_194
private theorem cert04_backward_leaf_192 : (cert04_L_0.contains) [4, 6, 7] = true := by decide +kernel
private theorem cert04_backward_192 : cert04_U_192.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6, 7] cert04_U_193 cert04_backward_leaf_192 cert04_backward_193
private theorem cert04_backward_leaf_191 : (cert04_L_0.contains) [4, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_191 : cert04_U_191.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 7, 15, 19] cert04_U_192 cert04_backward_leaf_191 cert04_backward_192
private theorem cert04_backward_leaf_190 : (cert04_L_0.contains) [4, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_190 : cert04_U_190.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 7, 18, 19] cert04_U_191 cert04_backward_leaf_190 cert04_backward_191
private theorem cert04_backward_leaf_189 : (cert04_L_0.contains) [4, 7, 19] = true := by decide +kernel
private theorem cert04_backward_189 : cert04_U_189.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 7, 19] cert04_U_190 cert04_backward_leaf_189 cert04_backward_190
private theorem cert04_backward_leaf_188 : (cert04_L_0.contains) [4, 7, 18] = true := by decide +kernel
private theorem cert04_backward_188 : cert04_U_188.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 7, 18] cert04_U_189 cert04_backward_leaf_188 cert04_backward_189
private theorem cert04_backward_leaf_187 : (cert04_L_0.contains) [4, 7, 15] = true := by decide +kernel
private theorem cert04_backward_187 : cert04_U_187.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 7, 15] cert04_U_188 cert04_backward_leaf_187 cert04_backward_188
private theorem cert04_backward_leaf_186 : (cert04_L_0.contains) [4, 12, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_186 : cert04_U_186.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12, 13, 15, 19] cert04_U_187 cert04_backward_leaf_186 cert04_backward_187
private theorem cert04_backward_leaf_185 : (cert04_L_0.contains) [4, 12, 13, 19] = true := by decide +kernel
private theorem cert04_backward_185 : cert04_U_185.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12, 13, 19] cert04_U_186 cert04_backward_leaf_185 cert04_backward_186
private theorem cert04_backward_leaf_184 : (cert04_L_0.contains) [4, 12, 13, 15] = true := by decide +kernel
private theorem cert04_backward_184 : cert04_U_184.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12, 13, 15] cert04_U_185 cert04_backward_leaf_184 cert04_backward_185
private theorem cert04_backward_leaf_183 : (cert04_L_0.contains) [4, 12, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_183 : cert04_U_183.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12, 14, 15, 19] cert04_U_184 cert04_backward_leaf_183 cert04_backward_184
private theorem cert04_backward_leaf_182 : (cert04_L_0.contains) [4, 12, 14, 19] = true := by decide +kernel
private theorem cert04_backward_182 : cert04_U_182.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12, 14, 19] cert04_U_183 cert04_backward_leaf_182 cert04_backward_183
private theorem cert04_backward_leaf_181 : (cert04_L_0.contains) [4, 12, 14, 15] = true := by decide +kernel
private theorem cert04_backward_181 : cert04_U_181.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12, 14, 15] cert04_U_182 cert04_backward_leaf_181 cert04_backward_182
private theorem cert04_backward_leaf_180 : (cert04_L_0.contains) [4, 12, 15, 19] = true := by decide +kernel
private theorem cert04_backward_180 : cert04_U_180.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12, 15, 19] cert04_U_181 cert04_backward_leaf_180 cert04_backward_181
private theorem cert04_backward_leaf_179 : (cert04_L_0.contains) [4, 12, 19] = true := by decide +kernel
private theorem cert04_backward_179 : cert04_U_179.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12, 19] cert04_U_180 cert04_backward_leaf_179 cert04_backward_180
private theorem cert04_backward_leaf_178 : (cert04_L_0.contains) [4, 12, 15] = true := by decide +kernel
private theorem cert04_backward_178 : cert04_U_178.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12, 15] cert04_U_179 cert04_backward_leaf_178 cert04_backward_179
private theorem cert04_backward_leaf_177 : (cert04_L_0.contains) [4, 12, 14] = true := by decide +kernel
private theorem cert04_backward_177 : cert04_U_177.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12, 14] cert04_U_178 cert04_backward_leaf_177 cert04_backward_178
private theorem cert04_backward_leaf_176 : (cert04_L_0.contains) [4, 12, 13] = true := by decide +kernel
private theorem cert04_backward_176 : cert04_U_176.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12, 13] cert04_U_177 cert04_backward_leaf_176 cert04_backward_177
private theorem cert04_backward_leaf_175 : (cert04_L_0.contains) [4, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_175 : cert04_U_175.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 13, 15, 19] cert04_U_176 cert04_backward_leaf_175 cert04_backward_176
private theorem cert04_backward_leaf_174 : (cert04_L_0.contains) [4, 13, 19] = true := by decide +kernel
private theorem cert04_backward_174 : cert04_U_174.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 13, 19] cert04_U_175 cert04_backward_leaf_174 cert04_backward_175
private theorem cert04_backward_leaf_173 : (cert04_L_0.contains) [4, 13, 15] = true := by decide +kernel
private theorem cert04_backward_173 : cert04_U_173.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 13, 15] cert04_U_174 cert04_backward_leaf_173 cert04_backward_174
private theorem cert04_backward_leaf_172 : (cert04_L_0.contains) [4, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_172 : cert04_U_172.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 14, 15, 19] cert04_U_173 cert04_backward_leaf_172 cert04_backward_173
private theorem cert04_backward_leaf_171 : (cert04_L_0.contains) [4, 14, 19] = true := by decide +kernel
private theorem cert04_backward_171 : cert04_U_171.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 14, 19] cert04_U_172 cert04_backward_leaf_171 cert04_backward_172
private theorem cert04_backward_leaf_170 : (cert04_L_0.contains) [4, 14, 15] = true := by decide +kernel
private theorem cert04_backward_170 : cert04_U_170.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 14, 15] cert04_U_171 cert04_backward_leaf_170 cert04_backward_171
private theorem cert04_backward_leaf_169 : (cert04_L_0.contains) [4, 15, 19] = true := by decide +kernel
private theorem cert04_backward_169 : cert04_U_169.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 15, 19] cert04_U_170 cert04_backward_leaf_169 cert04_backward_170
private theorem cert04_backward_leaf_168 : (cert04_L_0.contains) [4, 18, 19] = true := by decide +kernel
private theorem cert04_backward_168 : cert04_U_168.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 18, 19] cert04_U_169 cert04_backward_leaf_168 cert04_backward_169
private theorem cert04_backward_leaf_167 : (cert04_L_0.contains) [4, 19] = true := by decide +kernel
private theorem cert04_backward_167 : cert04_U_167.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 19] cert04_U_168 cert04_backward_leaf_167 cert04_backward_168
private theorem cert04_backward_leaf_166 : (cert04_L_0.contains) [4, 18] = true := by decide +kernel
private theorem cert04_backward_166 : cert04_U_166.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 18] cert04_U_167 cert04_backward_leaf_166 cert04_backward_167
private theorem cert04_backward_leaf_165 : (cert04_L_0.contains) [4, 15] = true := by decide +kernel
private theorem cert04_backward_165 : cert04_U_165.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 15] cert04_U_166 cert04_backward_leaf_165 cert04_backward_166
private theorem cert04_backward_leaf_164 : (cert04_L_0.contains) [4, 14] = true := by decide +kernel
private theorem cert04_backward_164 : cert04_U_164.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 14] cert04_U_165 cert04_backward_leaf_164 cert04_backward_165
private theorem cert04_backward_leaf_163 : (cert04_L_0.contains) [4, 13] = true := by decide +kernel
private theorem cert04_backward_163 : cert04_U_163.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 13] cert04_U_164 cert04_backward_leaf_163 cert04_backward_164
private theorem cert04_backward_leaf_162 : (cert04_L_0.contains) [4, 12] = true := by decide +kernel
private theorem cert04_backward_162 : cert04_U_162.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 12] cert04_U_163 cert04_backward_leaf_162 cert04_backward_163
private theorem cert04_backward_leaf_161 : (cert04_L_0.contains) [4, 7] = true := by decide +kernel
private theorem cert04_backward_161 : cert04_U_161.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 7] cert04_U_162 cert04_backward_leaf_161 cert04_backward_162
private theorem cert04_backward_leaf_160 : (cert04_L_0.contains) [4, 6] = true := by decide +kernel
private theorem cert04_backward_160 : cert04_U_160.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 6] cert04_U_161 cert04_backward_leaf_160 cert04_backward_161
private theorem cert04_backward_leaf_159 : (cert04_L_0.contains) [4, 5] = true := by decide +kernel
private theorem cert04_backward_159 : cert04_U_159.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4, 5] cert04_U_160 cert04_backward_leaf_159 cert04_backward_160
private theorem cert04_backward_leaf_158 : (cert04_L_0.contains) [5, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_158 : cert04_U_158.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 7, 15, 19] cert04_U_159 cert04_backward_leaf_158 cert04_backward_159
private theorem cert04_backward_leaf_157 : (cert04_L_0.contains) [5, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_157 : cert04_U_157.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 7, 18, 19] cert04_U_158 cert04_backward_leaf_157 cert04_backward_158
private theorem cert04_backward_leaf_156 : (cert04_L_0.contains) [5, 7, 19] = true := by decide +kernel
private theorem cert04_backward_156 : cert04_U_156.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 7, 19] cert04_U_157 cert04_backward_leaf_156 cert04_backward_157
private theorem cert04_backward_leaf_155 : (cert04_L_0.contains) [5, 7, 18] = true := by decide +kernel
private theorem cert04_backward_155 : cert04_U_155.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 7, 18] cert04_U_156 cert04_backward_leaf_155 cert04_backward_156
private theorem cert04_backward_leaf_154 : (cert04_L_0.contains) [5, 7, 15] = true := by decide +kernel
private theorem cert04_backward_154 : cert04_U_154.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 7, 15] cert04_U_155 cert04_backward_leaf_154 cert04_backward_155
private theorem cert04_backward_leaf_153 : (cert04_L_0.contains) [5, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_153 : cert04_U_153.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 13, 15, 19] cert04_U_154 cert04_backward_leaf_153 cert04_backward_154
private theorem cert04_backward_leaf_152 : (cert04_L_0.contains) [5, 13, 19] = true := by decide +kernel
private theorem cert04_backward_152 : cert04_U_152.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 13, 19] cert04_U_153 cert04_backward_leaf_152 cert04_backward_153
private theorem cert04_backward_leaf_151 : (cert04_L_0.contains) [5, 13, 15] = true := by decide +kernel
private theorem cert04_backward_151 : cert04_U_151.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 13, 15] cert04_U_152 cert04_backward_leaf_151 cert04_backward_152
private theorem cert04_backward_leaf_150 : (cert04_L_0.contains) [5, 15, 19] = true := by decide +kernel
private theorem cert04_backward_150 : cert04_U_150.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 15, 19] cert04_U_151 cert04_backward_leaf_150 cert04_backward_151
private theorem cert04_backward_leaf_149 : (cert04_L_0.contains) [5, 18, 19] = true := by decide +kernel
private theorem cert04_backward_149 : cert04_U_149.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 18, 19] cert04_U_150 cert04_backward_leaf_149 cert04_backward_150
private theorem cert04_backward_leaf_148 : (cert04_L_0.contains) [5, 19] = true := by decide +kernel
private theorem cert04_backward_148 : cert04_U_148.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 19] cert04_U_149 cert04_backward_leaf_148 cert04_backward_149
private theorem cert04_backward_leaf_147 : (cert04_L_0.contains) [5, 18] = true := by decide +kernel
private theorem cert04_backward_147 : cert04_U_147.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 18] cert04_U_148 cert04_backward_leaf_147 cert04_backward_148
private theorem cert04_backward_leaf_146 : (cert04_L_0.contains) [5, 15] = true := by decide +kernel
private theorem cert04_backward_146 : cert04_U_146.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 15] cert04_U_147 cert04_backward_leaf_146 cert04_backward_147
private theorem cert04_backward_leaf_145 : (cert04_L_0.contains) [5, 13] = true := by decide +kernel
private theorem cert04_backward_145 : cert04_U_145.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 13] cert04_U_146 cert04_backward_leaf_145 cert04_backward_146
private theorem cert04_backward_leaf_144 : (cert04_L_0.contains) [5, 7] = true := by decide +kernel
private theorem cert04_backward_144 : cert04_U_144.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5, 7] cert04_U_145 cert04_backward_leaf_144 cert04_backward_145
private theorem cert04_backward_leaf_143 : (cert04_L_0.contains) [6, 7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_143 : cert04_U_143.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 7, 15, 19] cert04_U_144 cert04_backward_leaf_143 cert04_backward_144
private theorem cert04_backward_leaf_142 : (cert04_L_0.contains) [6, 7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_142 : cert04_U_142.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 7, 18, 19] cert04_U_143 cert04_backward_leaf_142 cert04_backward_143
private theorem cert04_backward_leaf_141 : (cert04_L_0.contains) [6, 7, 19] = true := by decide +kernel
private theorem cert04_backward_141 : cert04_U_141.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 7, 19] cert04_U_142 cert04_backward_leaf_141 cert04_backward_142
private theorem cert04_backward_leaf_140 : (cert04_L_0.contains) [6, 7, 18] = true := by decide +kernel
private theorem cert04_backward_140 : cert04_U_140.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 7, 18] cert04_U_141 cert04_backward_leaf_140 cert04_backward_141
private theorem cert04_backward_leaf_139 : (cert04_L_0.contains) [6, 7, 15] = true := by decide +kernel
private theorem cert04_backward_139 : cert04_U_139.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 7, 15] cert04_U_140 cert04_backward_leaf_139 cert04_backward_140
private theorem cert04_backward_leaf_138 : (cert04_L_0.contains) [6, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_138 : cert04_U_138.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 14, 15, 19] cert04_U_139 cert04_backward_leaf_138 cert04_backward_139
private theorem cert04_backward_leaf_137 : (cert04_L_0.contains) [6, 14, 19] = true := by decide +kernel
private theorem cert04_backward_137 : cert04_U_137.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 14, 19] cert04_U_138 cert04_backward_leaf_137 cert04_backward_138
private theorem cert04_backward_leaf_136 : (cert04_L_0.contains) [6, 14, 15] = true := by decide +kernel
private theorem cert04_backward_136 : cert04_U_136.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 14, 15] cert04_U_137 cert04_backward_leaf_136 cert04_backward_137
private theorem cert04_backward_leaf_135 : (cert04_L_0.contains) [6, 15, 19] = true := by decide +kernel
private theorem cert04_backward_135 : cert04_U_135.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 15, 19] cert04_U_136 cert04_backward_leaf_135 cert04_backward_136
private theorem cert04_backward_leaf_134 : (cert04_L_0.contains) [6, 18, 19] = true := by decide +kernel
private theorem cert04_backward_134 : cert04_U_134.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 18, 19] cert04_U_135 cert04_backward_leaf_134 cert04_backward_135
private theorem cert04_backward_leaf_133 : (cert04_L_0.contains) [6, 19] = true := by decide +kernel
private theorem cert04_backward_133 : cert04_U_133.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 19] cert04_U_134 cert04_backward_leaf_133 cert04_backward_134
private theorem cert04_backward_leaf_132 : (cert04_L_0.contains) [6, 18] = true := by decide +kernel
private theorem cert04_backward_132 : cert04_U_132.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 18] cert04_U_133 cert04_backward_leaf_132 cert04_backward_133
private theorem cert04_backward_leaf_131 : (cert04_L_0.contains) [6, 15] = true := by decide +kernel
private theorem cert04_backward_131 : cert04_U_131.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 15] cert04_U_132 cert04_backward_leaf_131 cert04_backward_132
private theorem cert04_backward_leaf_130 : (cert04_L_0.contains) [6, 14] = true := by decide +kernel
private theorem cert04_backward_130 : cert04_U_130.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 14] cert04_U_131 cert04_backward_leaf_130 cert04_backward_131
private theorem cert04_backward_leaf_129 : (cert04_L_0.contains) [6, 7] = true := by decide +kernel
private theorem cert04_backward_129 : cert04_U_129.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6, 7] cert04_U_130 cert04_backward_leaf_129 cert04_backward_130
private theorem cert04_backward_leaf_128 : (cert04_L_0.contains) [7, 15, 19] = true := by decide +kernel
private theorem cert04_backward_128 : cert04_U_128.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [7, 15, 19] cert04_U_129 cert04_backward_leaf_128 cert04_backward_129
private theorem cert04_backward_leaf_127 : (cert04_L_0.contains) [7, 18, 19] = true := by decide +kernel
private theorem cert04_backward_127 : cert04_U_127.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [7, 18, 19] cert04_U_128 cert04_backward_leaf_127 cert04_backward_128
private theorem cert04_backward_leaf_126 : (cert04_L_0.contains) [7, 19] = true := by decide +kernel
private theorem cert04_backward_126 : cert04_U_126.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [7, 19] cert04_U_127 cert04_backward_leaf_126 cert04_backward_127
private theorem cert04_backward_leaf_125 : (cert04_L_0.contains) [7, 18] = true := by decide +kernel
private theorem cert04_backward_125 : cert04_U_125.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [7, 18] cert04_U_126 cert04_backward_leaf_125 cert04_backward_126
private theorem cert04_backward_leaf_124 : (cert04_L_0.contains) [7, 15] = true := by decide +kernel
private theorem cert04_backward_124 : cert04_U_124.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [7, 15] cert04_U_125 cert04_backward_leaf_124 cert04_backward_125
private theorem cert04_backward_leaf_123 : (cert04_L_0.contains) [8, 9, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_123 : cert04_U_123.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9, 11, 15, 19] cert04_U_124 cert04_backward_leaf_123 cert04_backward_124
private theorem cert04_backward_leaf_122 : (cert04_L_0.contains) [8, 9, 11, 19] = true := by decide +kernel
private theorem cert04_backward_122 : cert04_U_122.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9, 11, 19] cert04_U_123 cert04_backward_leaf_122 cert04_backward_123
private theorem cert04_backward_leaf_121 : (cert04_L_0.contains) [8, 9, 11, 15] = true := by decide +kernel
private theorem cert04_backward_121 : cert04_U_121.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9, 11, 15] cert04_U_122 cert04_backward_leaf_121 cert04_backward_122
private theorem cert04_backward_leaf_120 : (cert04_L_0.contains) [8, 9, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_120 : cert04_U_120.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9, 13, 15, 19] cert04_U_121 cert04_backward_leaf_120 cert04_backward_121
private theorem cert04_backward_leaf_119 : (cert04_L_0.contains) [8, 9, 13, 19] = true := by decide +kernel
private theorem cert04_backward_119 : cert04_U_119.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9, 13, 19] cert04_U_120 cert04_backward_leaf_119 cert04_backward_120
private theorem cert04_backward_leaf_118 : (cert04_L_0.contains) [8, 9, 13, 15] = true := by decide +kernel
private theorem cert04_backward_118 : cert04_U_118.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9, 13, 15] cert04_U_119 cert04_backward_leaf_118 cert04_backward_119
private theorem cert04_backward_leaf_117 : (cert04_L_0.contains) [8, 9, 15, 19] = true := by decide +kernel
private theorem cert04_backward_117 : cert04_U_117.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9, 15, 19] cert04_U_118 cert04_backward_leaf_117 cert04_backward_118
private theorem cert04_backward_leaf_116 : (cert04_L_0.contains) [8, 9, 19] = true := by decide +kernel
private theorem cert04_backward_116 : cert04_U_116.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9, 19] cert04_U_117 cert04_backward_leaf_116 cert04_backward_117
private theorem cert04_backward_leaf_115 : (cert04_L_0.contains) [8, 9, 15] = true := by decide +kernel
private theorem cert04_backward_115 : cert04_U_115.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9, 15] cert04_U_116 cert04_backward_leaf_115 cert04_backward_116
private theorem cert04_backward_leaf_114 : (cert04_L_0.contains) [8, 9, 13] = true := by decide +kernel
private theorem cert04_backward_114 : cert04_U_114.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9, 13] cert04_U_115 cert04_backward_leaf_114 cert04_backward_115
private theorem cert04_backward_leaf_113 : (cert04_L_0.contains) [8, 9, 11] = true := by decide +kernel
private theorem cert04_backward_113 : cert04_U_113.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9, 11] cert04_U_114 cert04_backward_leaf_113 cert04_backward_114
private theorem cert04_backward_leaf_112 : (cert04_L_0.contains) [8, 10, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_112 : cert04_U_112.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10, 11, 15, 19] cert04_U_113 cert04_backward_leaf_112 cert04_backward_113
private theorem cert04_backward_leaf_111 : (cert04_L_0.contains) [8, 10, 11, 19] = true := by decide +kernel
private theorem cert04_backward_111 : cert04_U_111.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10, 11, 19] cert04_U_112 cert04_backward_leaf_111 cert04_backward_112
private theorem cert04_backward_leaf_110 : (cert04_L_0.contains) [8, 10, 11, 15] = true := by decide +kernel
private theorem cert04_backward_110 : cert04_U_110.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10, 11, 15] cert04_U_111 cert04_backward_leaf_110 cert04_backward_111
private theorem cert04_backward_leaf_109 : (cert04_L_0.contains) [8, 10, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_109 : cert04_U_109.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10, 14, 15, 19] cert04_U_110 cert04_backward_leaf_109 cert04_backward_110
private theorem cert04_backward_leaf_108 : (cert04_L_0.contains) [8, 10, 14, 19] = true := by decide +kernel
private theorem cert04_backward_108 : cert04_U_108.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10, 14, 19] cert04_U_109 cert04_backward_leaf_108 cert04_backward_109
private theorem cert04_backward_leaf_107 : (cert04_L_0.contains) [8, 10, 14, 15] = true := by decide +kernel
private theorem cert04_backward_107 : cert04_U_107.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10, 14, 15] cert04_U_108 cert04_backward_leaf_107 cert04_backward_108
private theorem cert04_backward_leaf_106 : (cert04_L_0.contains) [8, 10, 15, 19] = true := by decide +kernel
private theorem cert04_backward_106 : cert04_U_106.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10, 15, 19] cert04_U_107 cert04_backward_leaf_106 cert04_backward_107
private theorem cert04_backward_leaf_105 : (cert04_L_0.contains) [8, 10, 19] = true := by decide +kernel
private theorem cert04_backward_105 : cert04_U_105.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10, 19] cert04_U_106 cert04_backward_leaf_105 cert04_backward_106
private theorem cert04_backward_leaf_104 : (cert04_L_0.contains) [8, 10, 15] = true := by decide +kernel
private theorem cert04_backward_104 : cert04_U_104.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10, 15] cert04_U_105 cert04_backward_leaf_104 cert04_backward_105
private theorem cert04_backward_leaf_103 : (cert04_L_0.contains) [8, 10, 14] = true := by decide +kernel
private theorem cert04_backward_103 : cert04_U_103.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10, 14] cert04_U_104 cert04_backward_leaf_103 cert04_backward_104
private theorem cert04_backward_leaf_102 : (cert04_L_0.contains) [8, 10, 11] = true := by decide +kernel
private theorem cert04_backward_102 : cert04_U_102.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10, 11] cert04_U_103 cert04_backward_leaf_102 cert04_backward_103
private theorem cert04_backward_leaf_101 : (cert04_L_0.contains) [8, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_101 : cert04_U_101.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 11, 15, 19] cert04_U_102 cert04_backward_leaf_101 cert04_backward_102
private theorem cert04_backward_leaf_100 : (cert04_L_0.contains) [8, 11, 19] = true := by decide +kernel
private theorem cert04_backward_100 : cert04_U_100.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 11, 19] cert04_U_101 cert04_backward_leaf_100 cert04_backward_101
private theorem cert04_backward_leaf_99 : (cert04_L_0.contains) [8, 11, 15] = true := by decide +kernel
private theorem cert04_backward_99 : cert04_U_99.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 11, 15] cert04_U_100 cert04_backward_leaf_99 cert04_backward_100
private theorem cert04_backward_leaf_98 : (cert04_L_0.contains) [8, 12, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_98 : cert04_U_98.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12, 13, 15, 19] cert04_U_99 cert04_backward_leaf_98 cert04_backward_99
private theorem cert04_backward_leaf_97 : (cert04_L_0.contains) [8, 12, 13, 19] = true := by decide +kernel
private theorem cert04_backward_97 : cert04_U_97.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12, 13, 19] cert04_U_98 cert04_backward_leaf_97 cert04_backward_98
private theorem cert04_backward_leaf_96 : (cert04_L_0.contains) [8, 12, 13, 15] = true := by decide +kernel
private theorem cert04_backward_96 : cert04_U_96.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12, 13, 15] cert04_U_97 cert04_backward_leaf_96 cert04_backward_97
private theorem cert04_backward_leaf_95 : (cert04_L_0.contains) [8, 12, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_95 : cert04_U_95.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12, 14, 15, 19] cert04_U_96 cert04_backward_leaf_95 cert04_backward_96
private theorem cert04_backward_leaf_94 : (cert04_L_0.contains) [8, 12, 14, 19] = true := by decide +kernel
private theorem cert04_backward_94 : cert04_U_94.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12, 14, 19] cert04_U_95 cert04_backward_leaf_94 cert04_backward_95
private theorem cert04_backward_leaf_93 : (cert04_L_0.contains) [8, 12, 14, 15] = true := by decide +kernel
private theorem cert04_backward_93 : cert04_U_93.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12, 14, 15] cert04_U_94 cert04_backward_leaf_93 cert04_backward_94
private theorem cert04_backward_leaf_92 : (cert04_L_0.contains) [8, 12, 15, 19] = true := by decide +kernel
private theorem cert04_backward_92 : cert04_U_92.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12, 15, 19] cert04_U_93 cert04_backward_leaf_92 cert04_backward_93
private theorem cert04_backward_leaf_91 : (cert04_L_0.contains) [8, 12, 19] = true := by decide +kernel
private theorem cert04_backward_91 : cert04_U_91.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12, 19] cert04_U_92 cert04_backward_leaf_91 cert04_backward_92
private theorem cert04_backward_leaf_90 : (cert04_L_0.contains) [8, 12, 15] = true := by decide +kernel
private theorem cert04_backward_90 : cert04_U_90.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12, 15] cert04_U_91 cert04_backward_leaf_90 cert04_backward_91
private theorem cert04_backward_leaf_89 : (cert04_L_0.contains) [8, 12, 14] = true := by decide +kernel
private theorem cert04_backward_89 : cert04_U_89.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12, 14] cert04_U_90 cert04_backward_leaf_89 cert04_backward_90
private theorem cert04_backward_leaf_88 : (cert04_L_0.contains) [8, 12, 13] = true := by decide +kernel
private theorem cert04_backward_88 : cert04_U_88.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12, 13] cert04_U_89 cert04_backward_leaf_88 cert04_backward_89
private theorem cert04_backward_leaf_87 : (cert04_L_0.contains) [8, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_87 : cert04_U_87.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 13, 15, 19] cert04_U_88 cert04_backward_leaf_87 cert04_backward_88
private theorem cert04_backward_leaf_86 : (cert04_L_0.contains) [8, 13, 19] = true := by decide +kernel
private theorem cert04_backward_86 : cert04_U_86.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 13, 19] cert04_U_87 cert04_backward_leaf_86 cert04_backward_87
private theorem cert04_backward_leaf_85 : (cert04_L_0.contains) [8, 13, 15] = true := by decide +kernel
private theorem cert04_backward_85 : cert04_U_85.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 13, 15] cert04_U_86 cert04_backward_leaf_85 cert04_backward_86
private theorem cert04_backward_leaf_84 : (cert04_L_0.contains) [8, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_84 : cert04_U_84.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 14, 15, 19] cert04_U_85 cert04_backward_leaf_84 cert04_backward_85
private theorem cert04_backward_leaf_83 : (cert04_L_0.contains) [8, 14, 19] = true := by decide +kernel
private theorem cert04_backward_83 : cert04_U_83.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 14, 19] cert04_U_84 cert04_backward_leaf_83 cert04_backward_84
private theorem cert04_backward_leaf_82 : (cert04_L_0.contains) [8, 14, 15] = true := by decide +kernel
private theorem cert04_backward_82 : cert04_U_82.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 14, 15] cert04_U_83 cert04_backward_leaf_82 cert04_backward_83
private theorem cert04_backward_leaf_81 : (cert04_L_0.contains) [8, 15, 19] = true := by decide +kernel
private theorem cert04_backward_81 : cert04_U_81.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 15, 19] cert04_U_82 cert04_backward_leaf_81 cert04_backward_82
private theorem cert04_backward_leaf_80 : (cert04_L_0.contains) [8, 19] = true := by decide +kernel
private theorem cert04_backward_80 : cert04_U_80.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 19] cert04_U_81 cert04_backward_leaf_80 cert04_backward_81
private theorem cert04_backward_leaf_79 : (cert04_L_0.contains) [8, 15] = true := by decide +kernel
private theorem cert04_backward_79 : cert04_U_79.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 15] cert04_U_80 cert04_backward_leaf_79 cert04_backward_80
private theorem cert04_backward_leaf_78 : (cert04_L_0.contains) [8, 14] = true := by decide +kernel
private theorem cert04_backward_78 : cert04_U_78.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 14] cert04_U_79 cert04_backward_leaf_78 cert04_backward_79
private theorem cert04_backward_leaf_77 : (cert04_L_0.contains) [8, 13] = true := by decide +kernel
private theorem cert04_backward_77 : cert04_U_77.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 13] cert04_U_78 cert04_backward_leaf_77 cert04_backward_78
private theorem cert04_backward_leaf_76 : (cert04_L_0.contains) [8, 12] = true := by decide +kernel
private theorem cert04_backward_76 : cert04_U_76.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 12] cert04_U_77 cert04_backward_leaf_76 cert04_backward_77
private theorem cert04_backward_leaf_75 : (cert04_L_0.contains) [8, 11] = true := by decide +kernel
private theorem cert04_backward_75 : cert04_U_75.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 11] cert04_U_76 cert04_backward_leaf_75 cert04_backward_76
private theorem cert04_backward_leaf_74 : (cert04_L_0.contains) [8, 10] = true := by decide +kernel
private theorem cert04_backward_74 : cert04_U_74.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 10] cert04_U_75 cert04_backward_leaf_74 cert04_backward_75
private theorem cert04_backward_leaf_73 : (cert04_L_0.contains) [8, 9] = true := by decide +kernel
private theorem cert04_backward_73 : cert04_U_73.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8, 9] cert04_U_74 cert04_backward_leaf_73 cert04_backward_74
private theorem cert04_backward_leaf_72 : (cert04_L_0.contains) [9, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_72 : cert04_U_72.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9, 11, 15, 19] cert04_U_73 cert04_backward_leaf_72 cert04_backward_73
private theorem cert04_backward_leaf_71 : (cert04_L_0.contains) [9, 11, 19] = true := by decide +kernel
private theorem cert04_backward_71 : cert04_U_71.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9, 11, 19] cert04_U_72 cert04_backward_leaf_71 cert04_backward_72
private theorem cert04_backward_leaf_70 : (cert04_L_0.contains) [9, 11, 15] = true := by decide +kernel
private theorem cert04_backward_70 : cert04_U_70.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9, 11, 15] cert04_U_71 cert04_backward_leaf_70 cert04_backward_71
private theorem cert04_backward_leaf_69 : (cert04_L_0.contains) [9, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_69 : cert04_U_69.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9, 13, 15, 19] cert04_U_70 cert04_backward_leaf_69 cert04_backward_70
private theorem cert04_backward_leaf_68 : (cert04_L_0.contains) [9, 13, 19] = true := by decide +kernel
private theorem cert04_backward_68 : cert04_U_68.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9, 13, 19] cert04_U_69 cert04_backward_leaf_68 cert04_backward_69
private theorem cert04_backward_leaf_67 : (cert04_L_0.contains) [9, 13, 15] = true := by decide +kernel
private theorem cert04_backward_67 : cert04_U_67.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9, 13, 15] cert04_U_68 cert04_backward_leaf_67 cert04_backward_68
private theorem cert04_backward_leaf_66 : (cert04_L_0.contains) [9, 15, 19] = true := by decide +kernel
private theorem cert04_backward_66 : cert04_U_66.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9, 15, 19] cert04_U_67 cert04_backward_leaf_66 cert04_backward_67
private theorem cert04_backward_leaf_65 : (cert04_L_0.contains) [9, 19] = true := by decide +kernel
private theorem cert04_backward_65 : cert04_U_65.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9, 19] cert04_U_66 cert04_backward_leaf_65 cert04_backward_66
private theorem cert04_backward_leaf_64 : (cert04_L_0.contains) [9, 15] = true := by decide +kernel
private theorem cert04_backward_64 : cert04_U_64.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9, 15] cert04_U_65 cert04_backward_leaf_64 cert04_backward_65
private theorem cert04_backward_leaf_63 : (cert04_L_0.contains) [9, 13] = true := by decide +kernel
private theorem cert04_backward_63 : cert04_U_63.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9, 13] cert04_U_64 cert04_backward_leaf_63 cert04_backward_64
private theorem cert04_backward_leaf_62 : (cert04_L_0.contains) [9, 11] = true := by decide +kernel
private theorem cert04_backward_62 : cert04_U_62.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9, 11] cert04_U_63 cert04_backward_leaf_62 cert04_backward_63
private theorem cert04_backward_leaf_61 : (cert04_L_0.contains) [10, 11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_61 : cert04_U_61.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10, 11, 15, 19] cert04_U_62 cert04_backward_leaf_61 cert04_backward_62
private theorem cert04_backward_leaf_60 : (cert04_L_0.contains) [10, 11, 19] = true := by decide +kernel
private theorem cert04_backward_60 : cert04_U_60.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10, 11, 19] cert04_U_61 cert04_backward_leaf_60 cert04_backward_61
private theorem cert04_backward_leaf_59 : (cert04_L_0.contains) [10, 11, 15] = true := by decide +kernel
private theorem cert04_backward_59 : cert04_U_59.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10, 11, 15] cert04_U_60 cert04_backward_leaf_59 cert04_backward_60
private theorem cert04_backward_leaf_58 : (cert04_L_0.contains) [10, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_58 : cert04_U_58.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10, 14, 15, 19] cert04_U_59 cert04_backward_leaf_58 cert04_backward_59
private theorem cert04_backward_leaf_57 : (cert04_L_0.contains) [10, 14, 19] = true := by decide +kernel
private theorem cert04_backward_57 : cert04_U_57.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10, 14, 19] cert04_U_58 cert04_backward_leaf_57 cert04_backward_58
private theorem cert04_backward_leaf_56 : (cert04_L_0.contains) [10, 14, 15] = true := by decide +kernel
private theorem cert04_backward_56 : cert04_U_56.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10, 14, 15] cert04_U_57 cert04_backward_leaf_56 cert04_backward_57
private theorem cert04_backward_leaf_55 : (cert04_L_0.contains) [10, 15, 19] = true := by decide +kernel
private theorem cert04_backward_55 : cert04_U_55.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10, 15, 19] cert04_U_56 cert04_backward_leaf_55 cert04_backward_56
private theorem cert04_backward_leaf_54 : (cert04_L_0.contains) [10, 19] = true := by decide +kernel
private theorem cert04_backward_54 : cert04_U_54.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10, 19] cert04_U_55 cert04_backward_leaf_54 cert04_backward_55
private theorem cert04_backward_leaf_53 : (cert04_L_0.contains) [10, 15] = true := by decide +kernel
private theorem cert04_backward_53 : cert04_U_53.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10, 15] cert04_U_54 cert04_backward_leaf_53 cert04_backward_54
private theorem cert04_backward_leaf_52 : (cert04_L_0.contains) [10, 14] = true := by decide +kernel
private theorem cert04_backward_52 : cert04_U_52.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10, 14] cert04_U_53 cert04_backward_leaf_52 cert04_backward_53
private theorem cert04_backward_leaf_51 : (cert04_L_0.contains) [10, 11] = true := by decide +kernel
private theorem cert04_backward_51 : cert04_U_51.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10, 11] cert04_U_52 cert04_backward_leaf_51 cert04_backward_52
private theorem cert04_backward_leaf_50 : (cert04_L_0.contains) [11, 15, 19] = true := by decide +kernel
private theorem cert04_backward_50 : cert04_U_50.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [11, 15, 19] cert04_U_51 cert04_backward_leaf_50 cert04_backward_51
private theorem cert04_backward_leaf_49 : (cert04_L_0.contains) [11, 19] = true := by decide +kernel
private theorem cert04_backward_49 : cert04_U_49.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [11, 19] cert04_U_50 cert04_backward_leaf_49 cert04_backward_50
private theorem cert04_backward_leaf_48 : (cert04_L_0.contains) [11, 15] = true := by decide +kernel
private theorem cert04_backward_48 : cert04_U_48.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [11, 15] cert04_U_49 cert04_backward_leaf_48 cert04_backward_49
private theorem cert04_backward_leaf_47 : (cert04_L_0.contains) [12, 13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_47 : cert04_U_47.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12, 13, 15, 19] cert04_U_48 cert04_backward_leaf_47 cert04_backward_48
private theorem cert04_backward_leaf_46 : (cert04_L_0.contains) [12, 13, 19] = true := by decide +kernel
private theorem cert04_backward_46 : cert04_U_46.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12, 13, 19] cert04_U_47 cert04_backward_leaf_46 cert04_backward_47
private theorem cert04_backward_leaf_45 : (cert04_L_0.contains) [12, 13, 15] = true := by decide +kernel
private theorem cert04_backward_45 : cert04_U_45.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12, 13, 15] cert04_U_46 cert04_backward_leaf_45 cert04_backward_46
private theorem cert04_backward_leaf_44 : (cert04_L_0.contains) [12, 14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_44 : cert04_U_44.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12, 14, 15, 19] cert04_U_45 cert04_backward_leaf_44 cert04_backward_45
private theorem cert04_backward_leaf_43 : (cert04_L_0.contains) [12, 14, 19] = true := by decide +kernel
private theorem cert04_backward_43 : cert04_U_43.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12, 14, 19] cert04_U_44 cert04_backward_leaf_43 cert04_backward_44
private theorem cert04_backward_leaf_42 : (cert04_L_0.contains) [12, 14, 15] = true := by decide +kernel
private theorem cert04_backward_42 : cert04_U_42.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12, 14, 15] cert04_U_43 cert04_backward_leaf_42 cert04_backward_43
private theorem cert04_backward_leaf_41 : (cert04_L_0.contains) [12, 15, 19] = true := by decide +kernel
private theorem cert04_backward_41 : cert04_U_41.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12, 15, 19] cert04_U_42 cert04_backward_leaf_41 cert04_backward_42
private theorem cert04_backward_leaf_40 : (cert04_L_0.contains) [12, 19] = true := by decide +kernel
private theorem cert04_backward_40 : cert04_U_40.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12, 19] cert04_U_41 cert04_backward_leaf_40 cert04_backward_41
private theorem cert04_backward_leaf_39 : (cert04_L_0.contains) [12, 15] = true := by decide +kernel
private theorem cert04_backward_39 : cert04_U_39.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12, 15] cert04_U_40 cert04_backward_leaf_39 cert04_backward_40
private theorem cert04_backward_leaf_38 : (cert04_L_0.contains) [12, 14] = true := by decide +kernel
private theorem cert04_backward_38 : cert04_U_38.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12, 14] cert04_U_39 cert04_backward_leaf_38 cert04_backward_39
private theorem cert04_backward_leaf_37 : (cert04_L_0.contains) [12, 13] = true := by decide +kernel
private theorem cert04_backward_37 : cert04_U_37.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12, 13] cert04_U_38 cert04_backward_leaf_37 cert04_backward_38
private theorem cert04_backward_leaf_36 : (cert04_L_0.contains) [13, 15, 19] = true := by decide +kernel
private theorem cert04_backward_36 : cert04_U_36.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [13, 15, 19] cert04_U_37 cert04_backward_leaf_36 cert04_backward_37
private theorem cert04_backward_leaf_35 : (cert04_L_0.contains) [13, 19] = true := by decide +kernel
private theorem cert04_backward_35 : cert04_U_35.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [13, 19] cert04_U_36 cert04_backward_leaf_35 cert04_backward_36
private theorem cert04_backward_leaf_34 : (cert04_L_0.contains) [13, 15] = true := by decide +kernel
private theorem cert04_backward_34 : cert04_U_34.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [13, 15] cert04_U_35 cert04_backward_leaf_34 cert04_backward_35
private theorem cert04_backward_leaf_33 : (cert04_L_0.contains) [14, 15, 19] = true := by decide +kernel
private theorem cert04_backward_33 : cert04_U_33.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [14, 15, 19] cert04_U_34 cert04_backward_leaf_33 cert04_backward_34
private theorem cert04_backward_leaf_32 : (cert04_L_0.contains) [14, 19] = true := by decide +kernel
private theorem cert04_backward_32 : cert04_U_32.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [14, 19] cert04_U_33 cert04_backward_leaf_32 cert04_backward_33
private theorem cert04_backward_leaf_31 : (cert04_L_0.contains) [14, 15] = true := by decide +kernel
private theorem cert04_backward_31 : cert04_U_31.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [14, 15] cert04_U_32 cert04_backward_leaf_31 cert04_backward_32
private theorem cert04_backward_leaf_30 : (cert04_L_0.contains) [15, 19] = true := by decide +kernel
private theorem cert04_backward_30 : cert04_U_30.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [15, 19] cert04_U_31 cert04_backward_leaf_30 cert04_backward_31
private theorem cert04_backward_leaf_29 : (cert04_L_0.contains) [16, 17, 18, 19] = true := by decide +kernel
private theorem cert04_backward_29 : cert04_U_29.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [16, 17, 18, 19] cert04_U_30 cert04_backward_leaf_29 cert04_backward_30
private theorem cert04_backward_leaf_28 : (cert04_L_0.contains) [16, 17, 19] = true := by decide +kernel
private theorem cert04_backward_28 : cert04_U_28.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [16, 17, 19] cert04_U_29 cert04_backward_leaf_28 cert04_backward_29
private theorem cert04_backward_leaf_27 : (cert04_L_0.contains) [16, 17, 18] = true := by decide +kernel
private theorem cert04_backward_27 : cert04_U_27.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [16, 17, 18] cert04_U_28 cert04_backward_leaf_27 cert04_backward_28
private theorem cert04_backward_leaf_26 : (cert04_L_0.contains) [16, 18, 19] = true := by decide +kernel
private theorem cert04_backward_26 : cert04_U_26.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [16, 18, 19] cert04_U_27 cert04_backward_leaf_26 cert04_backward_27
private theorem cert04_backward_leaf_25 : (cert04_L_0.contains) [16, 19] = true := by decide +kernel
private theorem cert04_backward_25 : cert04_U_25.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [16, 19] cert04_U_26 cert04_backward_leaf_25 cert04_backward_26
private theorem cert04_backward_leaf_24 : (cert04_L_0.contains) [16, 18] = true := by decide +kernel
private theorem cert04_backward_24 : cert04_U_24.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [16, 18] cert04_U_25 cert04_backward_leaf_24 cert04_backward_25
private theorem cert04_backward_leaf_23 : (cert04_L_0.contains) [16, 17] = true := by decide +kernel
private theorem cert04_backward_23 : cert04_U_23.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [16, 17] cert04_U_24 cert04_backward_leaf_23 cert04_backward_24
private theorem cert04_backward_leaf_22 : (cert04_L_0.contains) [17, 18, 19] = true := by decide +kernel
private theorem cert04_backward_22 : cert04_U_22.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [17, 18, 19] cert04_U_23 cert04_backward_leaf_22 cert04_backward_23
private theorem cert04_backward_leaf_21 : (cert04_L_0.contains) [17, 19] = true := by decide +kernel
private theorem cert04_backward_21 : cert04_U_21.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [17, 19] cert04_U_22 cert04_backward_leaf_21 cert04_backward_22
private theorem cert04_backward_leaf_20 : (cert04_L_0.contains) [17, 18] = true := by decide +kernel
private theorem cert04_backward_20 : cert04_U_20.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [17, 18] cert04_U_21 cert04_backward_leaf_20 cert04_backward_21
private theorem cert04_backward_leaf_19 : (cert04_L_0.contains) [18, 19] = true := by decide +kernel
private theorem cert04_backward_19 : cert04_U_19.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [18, 19] cert04_U_20 cert04_backward_leaf_19 cert04_backward_20
private theorem cert04_backward_leaf_18 : (cert04_L_0.contains) [19] = true := by decide +kernel
private theorem cert04_backward_18 : cert04_U_18.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [19] cert04_U_19 cert04_backward_leaf_18 cert04_backward_19
private theorem cert04_backward_leaf_17 : (cert04_L_0.contains) [18] = true := by decide +kernel
private theorem cert04_backward_17 : cert04_U_17.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [18] cert04_U_18 cert04_backward_leaf_17 cert04_backward_18
private theorem cert04_backward_leaf_16 : (cert04_L_0.contains) [17] = true := by decide +kernel
private theorem cert04_backward_16 : cert04_U_16.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [17] cert04_U_17 cert04_backward_leaf_16 cert04_backward_17
private theorem cert04_backward_leaf_15 : (cert04_L_0.contains) [16] = true := by decide +kernel
private theorem cert04_backward_15 : cert04_U_15.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [16] cert04_U_16 cert04_backward_leaf_15 cert04_backward_16
private theorem cert04_backward_leaf_14 : (cert04_L_0.contains) [15] = true := by decide +kernel
private theorem cert04_backward_14 : cert04_U_14.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [15] cert04_U_15 cert04_backward_leaf_14 cert04_backward_15
private theorem cert04_backward_leaf_13 : (cert04_L_0.contains) [14] = true := by decide +kernel
private theorem cert04_backward_13 : cert04_U_13.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [14] cert04_U_14 cert04_backward_leaf_13 cert04_backward_14
private theorem cert04_backward_leaf_12 : (cert04_L_0.contains) [13] = true := by decide +kernel
private theorem cert04_backward_12 : cert04_U_12.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [13] cert04_U_13 cert04_backward_leaf_12 cert04_backward_13
private theorem cert04_backward_leaf_11 : (cert04_L_0.contains) [12] = true := by decide +kernel
private theorem cert04_backward_11 : cert04_U_11.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [12] cert04_U_12 cert04_backward_leaf_11 cert04_backward_12
private theorem cert04_backward_leaf_10 : (cert04_L_0.contains) [11] = true := by decide +kernel
private theorem cert04_backward_10 : cert04_U_10.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [11] cert04_U_11 cert04_backward_leaf_10 cert04_backward_11
private theorem cert04_backward_leaf_9 : (cert04_L_0.contains) [10] = true := by decide +kernel
private theorem cert04_backward_9 : cert04_U_9.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [10] cert04_U_10 cert04_backward_leaf_9 cert04_backward_10
private theorem cert04_backward_leaf_8 : (cert04_L_0.contains) [9] = true := by decide +kernel
private theorem cert04_backward_8 : cert04_U_8.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [9] cert04_U_9 cert04_backward_leaf_8 cert04_backward_9
private theorem cert04_backward_leaf_7 : (cert04_L_0.contains) [8] = true := by decide +kernel
private theorem cert04_backward_7 : cert04_U_7.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [8] cert04_U_8 cert04_backward_leaf_7 cert04_backward_8
private theorem cert04_backward_leaf_6 : (cert04_L_0.contains) [7] = true := by decide +kernel
private theorem cert04_backward_6 : cert04_U_6.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [7] cert04_U_7 cert04_backward_leaf_6 cert04_backward_7
private theorem cert04_backward_leaf_5 : (cert04_L_0.contains) [6] = true := by decide +kernel
private theorem cert04_backward_5 : cert04_U_5.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [6] cert04_U_6 cert04_backward_leaf_5 cert04_backward_6
private theorem cert04_backward_leaf_4 : (cert04_L_0.contains) [5] = true := by decide +kernel
private theorem cert04_backward_4 : cert04_U_4.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [5] cert04_U_5 cert04_backward_leaf_4 cert04_backward_5
private theorem cert04_backward_leaf_3 : (cert04_L_0.contains) [4] = true := by decide +kernel
private theorem cert04_backward_3 : cert04_U_3.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [4] cert04_U_4 cert04_backward_leaf_3 cert04_backward_4
private theorem cert04_backward_leaf_2 : (cert04_L_0.contains) [3] = true := by decide +kernel
private theorem cert04_backward_2 : cert04_U_2.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [3] cert04_U_3 cert04_backward_leaf_2 cert04_backward_3
private theorem cert04_backward_leaf_1 : (cert04_L_0.contains) [2] = true := by decide +kernel
private theorem cert04_backward_1 : cert04_U_1.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [2] cert04_U_2 cert04_backward_leaf_1 cert04_backward_2
private theorem cert04_backward_leaf_0 : (cert04_L_0.contains) [1] = true := by decide +kernel
private theorem cert04_backward_0 : cert04_U_0.all (cert04_L_0.contains) = true :=
  cert04_all_cons (cert04_L_0.contains) [1] cert04_U_1 cert04_backward_leaf_0 cert04_backward_1
-- END CERTIFICATE04 PRIVATE DECOMPOSITION

theorem initial_check_3 : initialCheck 3 = true := by
  exact Bool.and_eq_true_iff.mpr
    ⟨(congrArg distinct cert04_U_eq).trans cert04_distinct_0,
      (congrArg (fun xs : List Cell => xs.all (fun c => (subfaces c).all xs.contains))
        cert04_I_eq).trans cert04_closed_0⟩
theorem cell_count_3 : («universe» 3).length = 391 := by decide +kernel
theorem initial_count_3 : (initial 3).length = 281 := by decide +kernel
theorem step_3_00 : stepCheck 3 (pairs3.take 0) (pairs3.getD 0 default) = true := by decide +kernel
theorem step_3_01 : stepCheck 3 (pairs3.take 1) (pairs3.getD 1 default) = true := by decide +kernel
theorem step_3_02 : stepCheck 3 (pairs3.take 2) (pairs3.getD 2 default) = true := by decide +kernel
theorem step_3_03 : stepCheck 3 (pairs3.take 3) (pairs3.getD 3 default) = true := by decide +kernel
theorem step_3_04 : stepCheck 3 (pairs3.take 4) (pairs3.getD 4 default) = true := by decide +kernel
theorem step_3_05 : stepCheck 3 (pairs3.take 5) (pairs3.getD 5 default) = true := by decide +kernel
theorem step_3_06 : stepCheck 3 (pairs3.take 6) (pairs3.getD 6 default) = true := by decide +kernel
theorem step_3_07 : stepCheck 3 (pairs3.take 7) (pairs3.getD 7 default) = true := by decide +kernel
theorem step_3_08 : stepCheck 3 (pairs3.take 8) (pairs3.getD 8 default) = true := by decide +kernel
theorem step_3_09 : stepCheck 3 (pairs3.take 9) (pairs3.getD 9 default) = true := by decide +kernel
theorem step_3_10 : stepCheck 3 (pairs3.take 10) (pairs3.getD 10 default) = true := by decide +kernel
theorem step_3_11 : stepCheck 3 (pairs3.take 11) (pairs3.getD 11 default) = true := by decide +kernel
theorem step_3_12 : stepCheck 3 (pairs3.take 12) (pairs3.getD 12 default) = true := by decide +kernel
theorem step_3_13 : stepCheck 3 (pairs3.take 13) (pairs3.getD 13 default) = true := by decide +kernel
theorem step_3_14 : stepCheck 3 (pairs3.take 14) (pairs3.getD 14 default) = true := by decide +kernel
theorem step_3_15 : stepCheck 3 (pairs3.take 15) (pairs3.getD 15 default) = true := by decide +kernel
theorem step_3_16 : stepCheck 3 (pairs3.take 16) (pairs3.getD 16 default) = true := by decide +kernel
theorem step_3_17 : stepCheck 3 (pairs3.take 17) (pairs3.getD 17 default) = true := by decide +kernel
theorem step_3_18 : stepCheck 3 (pairs3.take 18) (pairs3.getD 18 default) = true := by decide +kernel
theorem step_3_19 : stepCheck 3 (pairs3.take 19) (pairs3.getD 19 default) = true := by decide +kernel
theorem step_3_20 : stepCheck 3 (pairs3.take 20) (pairs3.getD 20 default) = true := by decide +kernel
theorem step_3_21 : stepCheck 3 (pairs3.take 21) (pairs3.getD 21 default) = true := by decide +kernel
theorem step_3_22 : stepCheck 3 (pairs3.take 22) (pairs3.getD 22 default) = true := by decide +kernel
theorem step_3_23 : stepCheck 3 (pairs3.take 23) (pairs3.getD 23 default) = true := by decide +kernel
theorem step_3_24 : stepCheck 3 (pairs3.take 24) (pairs3.getD 24 default) = true := by decide +kernel
theorem step_3_25 : stepCheck 3 (pairs3.take 25) (pairs3.getD 25 default) = true := by decide +kernel
theorem step_3_26 : stepCheck 3 (pairs3.take 26) (pairs3.getD 26 default) = true := by decide +kernel
theorem step_3_27 : stepCheck 3 (pairs3.take 27) (pairs3.getD 27 default) = true := by decide +kernel
theorem step_3_28 : stepCheck 3 (pairs3.take 28) (pairs3.getD 28 default) = true := by decide +kernel
theorem step_3_29 : stepCheck 3 (pairs3.take 29) (pairs3.getD 29 default) = true := by decide +kernel
theorem step_3_30 : stepCheck 3 (pairs3.take 30) (pairs3.getD 30 default) = true := by decide +kernel
theorem step_3_31 : stepCheck 3 (pairs3.take 31) (pairs3.getD 31 default) = true := by decide +kernel
theorem step_3_32 : stepCheck 3 (pairs3.take 32) (pairs3.getD 32 default) = true := by decide +kernel
theorem step_3_33 : stepCheck 3 (pairs3.take 33) (pairs3.getD 33 default) = true := by decide +kernel
theorem step_3_34 : stepCheck 3 (pairs3.take 34) (pairs3.getD 34 default) = true := by decide +kernel
theorem step_3_35 : stepCheck 3 (pairs3.take 35) (pairs3.getD 35 default) = true := by decide +kernel
theorem step_3_36 : stepCheck 3 (pairs3.take 36) (pairs3.getD 36 default) = true := by decide +kernel
theorem step_3_37 : stepCheck 3 (pairs3.take 37) (pairs3.getD 37 default) = true := by decide +kernel
theorem step_3_38 : stepCheck 3 (pairs3.take 38) (pairs3.getD 38 default) = true := by decide +kernel
theorem step_3_39 : stepCheck 3 (pairs3.take 39) (pairs3.getD 39 default) = true := by decide +kernel
theorem step_3_40 : stepCheck 3 (pairs3.take 40) (pairs3.getD 40 default) = true := by decide +kernel
theorem step_3_41 : stepCheck 3 (pairs3.take 41) (pairs3.getD 41 default) = true := by decide +kernel
theorem step_3_42 : stepCheck 3 (pairs3.take 42) (pairs3.getD 42 default) = true := by decide +kernel
theorem step_3_43 : stepCheck 3 (pairs3.take 43) (pairs3.getD 43 default) = true := by decide +kernel
theorem step_3_44 : stepCheck 3 (pairs3.take 44) (pairs3.getD 44 default) = true := by decide +kernel
theorem step_3_45 : stepCheck 3 (pairs3.take 45) (pairs3.getD 45 default) = true := by decide +kernel
theorem step_3_46 : stepCheck 3 (pairs3.take 46) (pairs3.getD 46 default) = true := by decide +kernel
theorem step_3_47 : stepCheck 3 (pairs3.take 47) (pairs3.getD 47 default) = true := by decide +kernel
theorem step_3_48 : stepCheck 3 (pairs3.take 48) (pairs3.getD 48 default) = true := by decide +kernel
theorem step_3_49 : stepCheck 3 (pairs3.take 49) (pairs3.getD 49 default) = true := by decide +kernel
theorem step_3_50 : stepCheck 3 (pairs3.take 50) (pairs3.getD 50 default) = true := by decide +kernel
theorem step_3_51 : stepCheck 3 (pairs3.take 51) (pairs3.getD 51 default) = true := by decide +kernel
theorem step_3_52 : stepCheck 3 (pairs3.take 52) (pairs3.getD 52 default) = true := by decide +kernel
theorem step_3_53 : stepCheck 3 (pairs3.take 53) (pairs3.getD 53 default) = true := by decide +kernel
theorem step_3_54 : stepCheck 3 (pairs3.take 54) (pairs3.getD 54 default) = true := by decide +kernel
theorem coverage_check_3 : coverageCheck 3 pairs3 = true := by
  exact ((congrArg (fun xs : List Cell => sameSet xs («universe» 3)) cert04_L_eq).trans
    (congrArg (sameSet cert04_L_0) cert04_U_eq)).trans
    (Bool.and_eq_true_iff.mpr ⟨cert04_forward_0, cert04_backward_0⟩)
theorem rank_check_3 : rankCheck pairs3 = true := by decide +kernel

end AutomaticCoherence.RelativeLastVertexLeanCertificate01
