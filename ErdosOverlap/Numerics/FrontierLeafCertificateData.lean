/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FrontierLeafGeometry
public import ErdosOverlap.FrontierWitnessModeFacts

/-!
# Executable native integral leaf certificates

These definitions are separated from analytic soundness so finite data can
be generated and checked without rebuilding the actual approximation proof.
Every claimed integral numerator uses the common integer scale `fixedScale`.
-/

@[expose] public section

namespace ErdosOverlap.FrontierLeaves

open Numerics

def auxiliaryLevel : ℚ := 380627425/1000000000
def boxCap : ℚ := 380629/1000000
def approximationError : ℚ := 2/1000000000000

def affineEval (a : RationalAffine) (t : ℚ) : ℚ := a.constant+a.slope*t

structure Capacities where
  L : RationalAffine
  U : RationalAffine
  K : RationalAffine
  V : RationalAffine
  deriving DecidableEq, Repr

def capacities (lo hi : ℚ) : Capacities :=
  let mid := (lo+hi)/2
  let L : RationalAffine := if mid < 2*auxiliaryLevel then ⟨2*auxiliaryLevel,-1⟩ else ⟨0,0⟩
  let U : RationalAffine := if mid < boxCap then ⟨0,1⟩ else ⟨boxCap,0⟩
  let K := if affineEval L mid ≤ affineEval U mid then L else U
  ⟨L,U,K,U.sub K⟩

def affineLeCheck (a b : RationalAffine) (lo hi : ℚ) : Bool :=
  decide (affineEval a lo ≤ affineEval b lo ∧ affineEval a hi ≤ affineEval b hi)

def capacityCheck (lo hi : ℚ) : Bool :=
  let mid := (lo+hi)/2
  let C := capacities lo hi
  (if mid < 2*auxiliaryLevel then decide (hi ≤ 2*auxiliaryLevel)
    else decide (2*auxiliaryLevel ≤ lo)) &&
  (if mid < boxCap then decide (hi ≤ boxCap) else decide (boxCap ≤ lo)) &&
  (if affineEval C.L mid ≤ affineEval C.U mid then affineLeCheck C.L C.U lo hi
    else affineLeCheck C.U C.L lo hi)

def profileWeights (g : Geometry) (lam : ℚ) : LeafWeights :=
  let C := capacities g.left g.right
  conjugateWeights g.cache.rangeA g.cache.rangeB lam C.L C.K C.V

def centralWeights (g : Geometry) : LeafWeights :=
  ⟨⟨0,0⟩, (capacities g.left g.right).L.scale
    (boxPositiveSelector g.cache.rangeB : ℚ), ⟨0,0⟩⟩

def denominatorWeights (g : Geometry) : LeafWeights :=
  let lineA := g.cache.rangeA.positiveLine
  let lineB := g.cache.rangeB.positiveLine
  ⟨⟨2*lineA.slope,0⟩,⟨2*lineB.slope,0⟩,⟨2*(lineA.constant+lineB.constant),0⟩⟩

structure ProfileLeaf where
  geometry : CheckedGeometry
  cell : Option ℕ
  lam : ℚ
  lower : ℤ

def ProfileLeaf.check (leaf : ProfileLeaf) (mode : Fin 20) : Bool :=
  let g := leaf.geometry.val
  capacityCheck g.left g.right &&
  FrontierWitnesses.slopeLeafCheck mode leaf.cell g.left g.right leaf.lam &&
  decide (leaf.lower ≤
    ((profileWeights g leaf.lam).integralBox g.cache.integrals g.left g.right).lo)

def CheckedProfileLeaf (mode : Fin 20) := {leaf : ProfileLeaf // leaf.check mode = true}

structure CentralLeaf where
  geometry : CheckedGeometry
  lower : ℤ

def CentralLeaf.check (leaf : CentralLeaf) : Bool :=
  let g := leaf.geometry.val
  capacityCheck g.left g.right &&
  decide (leaf.lower ≤
    ((centralWeights g).integralBox g.cache.integrals g.left g.right).lo)

def CheckedCentralLeaf := {leaf : CentralLeaf // leaf.check = true}

structure DenominatorLeaf where
  geometry : CheckedGeometry
  upper : ℤ

def DenominatorLeaf.check (leaf : DenominatorLeaf) : Bool :=
  let g := leaf.geometry.val
  decide (((denominatorWeights g).integralBox g.cache.integrals g.left g.right).hi ≤ leaf.upper)

def CheckedDenominatorLeaf := {leaf : DenominatorLeaf // leaf.check = true}

def ProfileLeaf.lowerBound (leaf : ProfileLeaf) : ℚ :=
  (leaf.lower : ℚ)/fixedScale-
    2*approximationError*(leaf.geometry.val.right-leaf.geometry.val.left)

def CentralLeaf.lowerBound (leaf : CentralLeaf) : ℚ :=
  (leaf.lower : ℚ)/fixedScale-
    2*approximationError*(leaf.geometry.val.right-leaf.geometry.val.left)

def DenominatorLeaf.upperBound (leaf : DenominatorLeaf) : ℚ :=
  (leaf.upper : ℚ)/fixedScale+
    4*approximationError*(leaf.geometry.val.right-leaf.geometry.val.left)

end ErdosOverlap.FrontierLeaves
