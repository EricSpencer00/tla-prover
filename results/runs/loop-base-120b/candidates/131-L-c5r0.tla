---- MODULE MajorityProof ----
EXTENDS Majority

CONSTANT Value

(*--------------------------------------------------------------------
  Specification of the system.  It reuses the initial predicate and
  next-state relation from the main Majority module.
--------------------------------------------------------------------*)
Spec == Majority.Init /\ [][Majority.Next]_(Majority.vars)

(*--------------------------------------------------------------------
  Invariants required by the configuration.  They are simply aliases
  for the corresponding predicates defined in the main specification.
--------------------------------------------------------------------*)
TypeOK == Majority.TypeOK
Correct == Majority.Correct
Inv     == Majority.Inv

====