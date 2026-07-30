---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

\* Concrete values used in the majority vote sequences.
Elements == {A, B, C}

\* Sequences of actual bounded length: for each n up to the bound, the set of
\* functions with domain 1..n over the element set. This keeps the state space
\* finite for model checking.
Seqs == UNION { [1..n -> Elements] : n \in 0..bound }

VARIABLES seq, pos, can, cnt

vars == <<seq, pos, can, cnt>>

TypeOK ==
    /\ seq \in Seqs
    /\ pos \in 1..(bound + 1)
    /\ can \in Elements
    /\ cnt \in 0..bound

\* The main correctness property: any true majority element must be the final
\* candidate, provided the scan has completed and the counter is non-zero.
Correct ==
    \A v \in Elements :
        (2 * Cardinality({ i \in DOMAIN seq : seq[i] = v }) > Cardinality(DOMAIN seq))
            => (pos = bound + 1 /\ cnt > 0 /\ can = v)

\* The inductive invariant from the main specification.
Inv ==
    /\ cnt = 0 => can \in Elements
    /\ cnt > 0 => can \in Elements
    /\ pos <= Cardinality(DOMAIN seq) + 1

Init ==
    /\ seq \in Seqs
    /\ pos = 1
    /\ can \in Elements
    /\ cnt = 0

\* The three-case scan: adopt a new candidate, increment, or decrement.
Step ==
    /\ pos <= Cardinality(DOMAIN seq)
    /\ LET x == seq[pos] IN
        /\ IF cnt = 0 THEN can' = x /\ cnt' = 1
           ELSE IF can = x THEN cnt' = cnt + 1
           ELSE cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====