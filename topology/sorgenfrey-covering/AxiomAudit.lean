import SorgenfreyCovering

#print axioms Counterexample.SorgenfreyLine.countable_Ico_cover
#print axioms Counterexample.SorgenfreyLine.isLindelof_set
#print axioms Counterexample.SorgenfreyLine.instHereditarilyLindelofSpace
#print axioms Counterexample.SorgenfreyLine.disjointify_clopen_cover
#print axioms Counterexample.SorgenfreyLine.clopen_refinement
#print axioms Counterexample.SorgenfreyLine.instParacompactSpace_subspace
#print axioms Counterexample.SorgenfreyLine.instParacompactSpace
#print axioms Counterexample.SorgenfreyLine.not_lindelofSpace_prod
#print axioms Counterexample.SorgenfreyLine.not_paracompactSpace_prod

-- Concrete instance checks, in addition to auditing the declarations above.
example (A : Set Counterexample.SorgenfreyLine) : LindelofSpace A :=
  isLindelof_iff_lindelofSpace.1 (Counterexample.SorgenfreyLine.isLindelof_set A)
example (A : Set Counterexample.SorgenfreyLine) : ParacompactSpace A := inferInstance
example : LindelofSpace Counterexample.SorgenfreyLine := inferInstance
example : ParacompactSpace Counterexample.SorgenfreyLine := inferInstance
