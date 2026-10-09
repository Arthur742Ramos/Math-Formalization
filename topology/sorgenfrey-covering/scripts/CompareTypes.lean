module

public import StatementSpecifications
public import Solution

-- Each independent proposition is checked against the complete exported proof.
-- No assumptions, coercions of predicates, or theorem holes are introduced.
example : SorgenfreyChallenge.isLindelof_set :=
  Counterexample.SorgenfreyLine.isLindelof_set
example : SorgenfreyChallenge.hereditary_lindelof :=
  Counterexample.SorgenfreyLine.instHereditarilyLindelofSpace
example : SorgenfreyChallenge.clopen_refinement :=
  @Counterexample.SorgenfreyLine.clopen_refinement
example : SorgenfreyChallenge.paracompact_subspaces :=
  Counterexample.SorgenfreyLine.instParacompactSpace_subspace
example : SorgenfreyChallenge.paracompact_line :=
  Counterexample.SorgenfreyLine.instParacompactSpace
example : SorgenfreyChallenge.plane_not_lindelof :=
  Counterexample.SorgenfreyLine.not_lindelofSpace_prod
example : SorgenfreyChallenge.plane_not_paracompact :=
  Counterexample.SorgenfreyLine.not_paracompactSpace_prod
