---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

\* ---------- Constants ----------
CONSTANT A, B, C, bound, Seq

\* ---------- Derived constant ----------
Values == {A, B, C}

\* ---------- State variables ----------
VARIABLES pos, cand, cnt, seq

\* ---------- Helper definitions ----------
PosRange == 1 .. bound

\* ---------- Initial predicate ----------
Init ==
  /\ pos \in PosRange
  /\ cand \in Values
  /\ cnt = 0
  /\ seq \in [1..bound -> Values]  \* any bounded sequence of length ≤ bound

\* ---------- Actions ----------
Scan ==
  \/ /\ pos < bound
        /\ \E i \in Values :
              /\ i = seq[pos + 1]
              /\ IF cnt = 0
                    THEN cand' = i /\ cnt' = 1
                    ELSE IF cand = i
                            THEN cnt' = cnt + 1
                            ELSE cnt' = cnt - 1
     /\ pos' = pos + 1
  \/ /\ pos = bound
        /\ UNCHANGED <<pos, cand, cnt, seq>>

Next == Scan

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<pos, cand, cnt, seq>>

\* ---------- Invariant ----------
Inv ==
  /\ pos \in PosRange
  /\ cand \in Values
  /\ cnt \in Nat
  /\ seq \in [1..bound -> Values]

\* ---------- Type correctness invariant ----------
TypeOK == Inv

\* ---------- Correctness invariant ----------
Correct ==
  (\E v \in Values :
        (Cardinality({ i \in 1..bound : seq[i] = v }) > bound / 2) => cand = v)

\* ---------- Liveness property ----------
ScanDone == pos = bound

=============================================================================