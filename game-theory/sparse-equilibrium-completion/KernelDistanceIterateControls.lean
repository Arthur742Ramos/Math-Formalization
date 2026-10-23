module
public import RationalFeatureIterate
public import CachedResidualDistance
public meta import RationalFeatureIterate
public meta import CachedResidualDistance
@[expose] public section
open SparseCompletion
#guard rationalFeatureKernel (d:=0) (m:=0) (fun _ _ => 0) (fun _ => 0) = none
#guard rationalFeatureKernel (d:=1) (m:=1) (fun _ _ => 1) (fun _ => 1) = none
#guard rationalFeatureCompressWithMass (d:=0) (m:=0) (fun _ _ => 0) (fun _ => 0) = (fun _ => 0)
#guard rationalFeatureCompressWithMass (d:=0) (m:=1) (fun _ _ => 0) (fun _ => 1) 0 = 1
#guard rationalFeatureCompressWithMass (d:=0) (m:=2) (fun _ _ => 0) (fun _ => 1/2) 0 = 0
#guard rationalFeatureCompressWithMass (d:=0) (m:=2) (fun _ _ => 0) (fun _ => 1/2) 1 = 1
#guard rationalFeatureIterates (d:=1) (m:=2) (fun _ _ => 1) (fun _ => 1/2) 0 0 = 1/2
#guard cachedBFSDistance (n:=3) (Vector.ofFn fun u => Vector.ofFn fun v => decide (u.val+1=v.val)) 0 0 = 0
#guard cachedBFSDistance (n:=3) (Vector.ofFn fun u => Vector.ofFn fun v => decide (u.val+1=v.val)) 0 2 = 2
#guard cachedBFSDistance (n:=3) (Vector.ofFn fun u => Vector.ofFn fun v => decide (u.val+1=v.val)) 2 0 = 4
#guard cachedBFSDistance (n:=3) (Vector.ofFn fun _ => Vector.ofFn fun _ => true) 0 2 = 1
#guard cachedBFSDistance (n:=1) (Vector.ofFn fun _ => Vector.ofFn fun _ => false) 0 0 = 0
