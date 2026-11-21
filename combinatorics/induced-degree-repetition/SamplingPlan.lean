module

public import HostScales
public import BlockSizes
public import SampledWitness
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition.Sampling

open Finset OpenProblems
open scoped Classical

/-- Finite numerical conditions for selecting testers and positional pools.
All quantities are fixed before sampling vertices from the core. -/
structure SamplingPlan (r M g L₀ L₁ n₁ : ℕ) (u θ η a ε : ℝ) where
  k : ℕ
  s : ℕ
  m : ℕ
  b : ℕ
  v : ℝ
  κ : ℝ
  count : ℝ
  D : ℝ
  block : k*(L₀+L₁)=m
  enough : n₁ ≤ k
  poly : k+k ≤ r^2
  fresh : (s:ℝ) ≤ a*r
  ext : (g-1)*s ≤ 4*r
  nh : 4*r ≤ g*s
  tail : g*m < r
  positive : 0 < b
  testSize : M ≤ 3*(M/2)
  testPos : 0 < M/2
  space : g*m*b+M/2 ≤ M
  cutoff : (M:ℝ)*Real.exp (-u*r/16) ≤ b
  half : b ≤ M/2
  vpos : 0 < v
  κpos : 0 < κ
  cpos : 0 < count
  margin : 2+((g:ℝ)+2)*v ≤ θ*m
  exceptional : (2*r:ℕ)*κ/v^2+count+(g*m:ℕ) ≤ η*r
  collisions : ((g*s:ℕ):ℝ)^2/(M/2:ℕ) ≤ 1/8
  spectral : ((g*s:ℕ):ℝ)^4*(9*ε^2)+6*((g*s:ℕ):ℝ)^3 ≤ κ^2/8
  variance : 2*((k+k:ℕ):ℝ)*L₁^2+2*(ε*M)^2*m/((b:ℝ)*(M/2:ℕ)) ≤ D
  refErrors : ((g*s:ℕ):ℝ)*(g*(D/v^2)) ≤ count/8

end InducedDegreeRepetition.Sampling
