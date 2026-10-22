/- AI-assisted executable regression controls. Apache-2.0. -/
module
public import RationalCountedCertificateSoundness
public import RationalTableStorage
public meta import RationalCountedCertificateSoundness
public meta import RationalCountedTableCertificate
public meta import RationalCountedTableRows
public meta import RationalCountedAll
public meta import RationalCountedDot
public meta import RationalTableCertificate
public meta import RationalTableStorage
@[expose] public section
open SparseCompletion

def countedTestCertificate (p q b : ℚ) : RationalTableCertificate 1 3 1 where
  labels := #v[(1 : Fin 3)]
  anchors := #v[p]
  weights := #v[q]
  residual := #v[#v[b]]
  labelsInjective := by intro i j _; exact Subsingleton.elim i j

def countedTestK : Vector (Vector ℚ 1) 1 := #v[#v[0]]
def countedTestD : Vector (Vector ℚ 1) 3 := #v[#v[0],#v[0],#v[0]]
def countedTestOmittedD : Vector (Vector ℚ 1) 3 := #v[#v[1],#v[0],#v[0]]

#guard (rationalCountedTableCertificate (countedTestCertificate (1/2) (1/2) 0) countedTestK countedTestD 1 0).1
#guard (rationalCountedTableCertificate (countedTestCertificate (1/2) (1/2) 0) countedTestK countedTestD 1 0).2=46
#guard !(rationalCountedTableCertificate (countedTestCertificate (1/2) (1/4) 0) countedTestK countedTestD 1 0).1
#guard !(rationalCountedTableCertificate (countedTestCertificate (1/2) (1/2) 0) countedTestK countedTestD (-1) 0).1
#guard !(rationalCountedTableCertificate (countedTestCertificate (1/2) (1/2) 1) countedTestK countedTestD 1 0).1
#guard !(rationalCountedTableCertificate (countedTestCertificate (3/2) (-1/2) 0) countedTestK countedTestD 1 0).1
#guard !(rationalCountedTableCertificate (countedTestCertificate (-1/2) (3/2) 0) countedTestK countedTestD 1 0).1
#guard (rationalCountedTableCertificate (countedTestCertificate 1 0 0) countedTestK countedTestD 1 0).1
#guard !(rationalCountedTableCertificate (countedTestCertificate (3/4) (1/4) 0) countedTestK countedTestOmittedD 1 0).1
#guard rationalTableScalarSlots (countedTestCertificate (1/2) (1/2) 0)=3
#guard rationalObservationScalarSlots countedTestK countedTestD=4

def countedResidualOnly (m : ℕ) (hm : 0 < m) : RationalTableCertificate 0 m 1 where
  labels := #v[⟨0,hm⟩]
  anchors := #v[]
  weights := #v[1]
  residual := #v[#v[0]]
  labelsInjective := by intro i j _; exact Subsingleton.elim i j

#guard (rationalCountedTableCertificate (countedResidualOnly 3 (by decide))
  #v[] (Vector.replicate 3 #v[]) 1 0).1
#guard (rationalCountedTableCertificate (countedResidualOnly 3 (by decide))
  #v[] (Vector.replicate 3 #v[]) 1 0).2=20
#guard (rationalCountedTableCertificate (countedResidualOnly 5 (by decide))
  #v[] (Vector.replicate 5 #v[]) 1 0).2=20

def countedNoResidual : RationalTableCertificate 1 0 0 where
  labels := #v[]
  anchors := #v[1]
  weights := #v[]
  residual := #v[]
  labelsInjective := fun i => Fin.elim0 i
#guard (rationalCountedTableCertificate countedNoResidual countedTestK #v[] 1 0).1

def countedEmpty : RationalTableCertificate 0 0 0 where
  labels := #v[]
  anchors := #v[]
  weights := #v[]
  residual := #v[]
  labelsInjective := fun i => Fin.elim0 i
#guard !(rationalCountedTableCertificate countedEmpty #v[] #v[] 1 0).1
