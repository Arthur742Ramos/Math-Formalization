/- AI-assisted executable regression controls. Apache-2.0. -/
module
public import RationalCountedIntervalObservations
public import RationalCountedCertificateChecks
public meta import RationalCountedIntervalObservations
public meta import RationalCountedCommitments
public meta import RationalCountedCertificateChecks
@[expose] public section
open SparseCompletion

#guard (rationalCountedFixedCertificate (countedTestCertificate (1/2) (1/2) 0)
  countedTestK countedTestD 1 0 #v[(1/2 : ℚ)]).1
#guard !(rationalCountedFixedCertificate (countedTestCertificate (1/2) (1/2) 0)
  countedTestK countedTestD 1 0 #v[(3/4 : ℚ)]).1
#guard (rationalCountedFloorCertificate (countedTestCertificate (1/2) (1/2) 0)
  countedTestK countedTestD 1 0 #v[(1/4 : ℚ)]).1
#guard !(rationalCountedFloorCertificate (countedTestCertificate (1/2) (1/2) 0)
  countedTestK countedTestD 1 0 #v[(3/4 : ℚ)]).1
#guard (rationalCountedFixedCertificate (countedTestCertificate (1/2) (1/2) 0)
  countedTestK countedTestD 1 0 #v[(1/2 : ℚ)]).2=47
#guard (rationalCountedFloorCertificate (countedTestCertificate (1/2) (1/2) 0)
  countedTestK countedTestD 1 0 #v[(1/4 : ℚ)]).2=47

#guard (rationalCountedIntervalFixedCertificate (countedTestCertificate (1/2) (1/2) 0)
  countedTestK countedTestK countedTestK countedTestD countedTestD countedTestD 1 0 #v[(1/2 : ℚ)]).1
#guard (rationalCountedIntervalFloorCertificate (countedTestCertificate (1/2) (1/2) 0)
  countedTestK countedTestK countedTestK countedTestD countedTestD countedTestD 1 0 #v[(1/4 : ℚ)]).1
#guard (rationalCountedIntervalFixedCertificate (countedTestCertificate (1/2) (1/2) 0)
  countedTestK countedTestK countedTestK countedTestD countedTestD countedTestD 1 0 #v[(1/2 : ℚ)]).2=55
#guard !(rationalCountedIntervalFixedCertificate (countedTestCertificate (1/2) (1/2) 0)
  countedTestK countedTestK countedTestK countedTestD countedTestD #v[#v[(-1/4 : ℚ)],#v[0],#v[0]]
  1 0 #v[(1/2 : ℚ)]).1
#guard !(rationalCountedIntervalFloorCertificate (countedTestCertificate (1/2) (1/2) 0)
  countedTestK #v[#v[(1/4 : ℚ)]] countedTestK countedTestD countedTestD countedTestD
  1 0 #v[(1/4 : ℚ)]).1
#guard (rationalCountedIntervalFixedCertificate (countedResidualOnly 3 (by decide))
  #v[] #v[] #v[] (Vector.replicate 3 #v[]) (Vector.replicate 3 #v[]) (Vector.replicate 3 #v[])
  1 0 #v[]).2=20
