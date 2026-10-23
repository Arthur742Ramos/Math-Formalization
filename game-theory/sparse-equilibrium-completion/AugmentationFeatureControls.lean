module
public import RationalFlowLattice
public import RationalFlowEncodingBounds
public import RationalFeatureDeletion
public meta import RationalFlowLattice
public meta import RationalFlowEncodingBounds
public meta import RationalFeatureDeletion
@[expose] public section
open SparseCompletion
#guard rationalNonemptyMinimum [] = none
#guard rationalNonemptyMinimum [2,3] = some 2
#guard rationalNonemptyMinimum [5/4,1/2,2] = some (1/2)
#guard rationalNonemptyMinimum [0,2] = some 0
#guard rationalNonemptyMinimum [-2,-3] = some (-3)
#guard rationalNetPushPath (n:=3) (fun _ _ => 0) 0 [1,2] 1 0 1 = 1
#guard rationalNetPushPath (n:=3) (fun _ _ => 0) 0 [1,2] 1 1 2 = 1
#guard rationalNetPushPath (n:=3) (fun _ _ => 0) 0 [1,2] 1 1 0 = -1
#guard rationalNetPushPath (n:=3) (fun _ _ => 0) 0 [1,2] 1 0 2 = 0
#guard rationalNetPushPath (n:=2) (fun _ _ => 3/4) 0 [] 100 0 1 = 3/4
#guard rationalFeatureTheta (m:=2) (fun _ => 1/2) (fun i => if i=0 then 1 else -1) = 1/2
#guard rationalFeatureDelete (m:=2) (fun _ => 1/2) (fun i => if i=0 then 1 else -1) 0 = 0
#guard rationalFeatureDelete (m:=2) (fun _ => 1/2) (fun i => if i=0 then 1 else -1) 1 = 1
#guard rationalFeatureTheta (m:=2) (fun _ => 1/2) (fun _ => 0) = 0
#guard rationalFeatureDelete (m:=2) (fun _ => 1/2) (fun _ => 0) 0 = 1/2
#guard rationalFeatureDelete (m:=3) (fun i => if i=2 then 1/2 else 1/4) (fun i => if i=2 then -2 else 1) 2 = 1
#guard rationalCapacityDenominator (n:=0) (fun _ _ => 0) = 1
#guard rationalCapacityDenominator (n:=2) (fun u v => if u=0 then (if v=0 then 1/2 else 1/3) else (if v=0 then 2/3 else 1/4)) = 72
#guard rationalCanonicalEncodingBits (3/4) = 6
#guard rationalCanonicalEncodingBits 0 = 3
