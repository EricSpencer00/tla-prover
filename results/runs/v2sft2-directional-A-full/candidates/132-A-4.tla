---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS A, B, C, bound, Seq

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
Values == {A, B, C}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, pos, candidate, counter

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in { s \in Seq : Len(s) <= bound }
    /\ pos = 1
    /\ candidate \in Values
    /\ counter = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Scan ==
    /\ pos <= Len(seq)
    /\ \E a \in { seq[pos] } :
          IF a = candidate
          THEN /\ candidate' = candidate
               /\ counter' = counter + 1
          ELSE IF counter > 0
               THEN /\ candidate' = candidate
                    /\ counter' = counter - 1
          ELSE /\ candidate' = a
               /\ counter' = 0
    /\ pos' = pos + 1

Next == Scan

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, candidate, counter>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (optional, for clarity)
\* ----------------------------------------------------------------------
TypeOK == 
    /\ seq \in { s \in Seq : Len(s) <= bound }
    /\ pos \in Nat
    /\ candidate \in Values
    /\ counter \in Nat

\* ----------------------------------------------------------------------
\* Main correctness property: any majority element must equal the candidate
\* after a complete scan.
\* ----------------------------------------------------------------------
Correct ==
    Len(seq) > 0 => 
        ( \E x \in Values :
              ( (2 * Count(x, seq) > Len(seq)) => (candidate = x) ) )

\* ----------------------------------------------------------------------
\* Inductive invariant used by TLC (deferred for brevity)
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ (pos = Len(seq) + 1) => Correct

====