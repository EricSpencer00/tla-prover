---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, Majority

CONSTANT Value

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Majority.Spec

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK == Majority.TypeOK
Inv    == Majority.Inv

(*--------------------------------------------------------------------
  Correctness property:
  After the whole sequence has been processed (i = Len(seq)),
  any value that occurs in a strict majority of positions must be
  the current candidate.
--------------------------------------------------------------------*)
Correct ==
    ( i = Len(seq) =>
        \A v \in Value :
            ( Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2 )
                => v = candidate )

====