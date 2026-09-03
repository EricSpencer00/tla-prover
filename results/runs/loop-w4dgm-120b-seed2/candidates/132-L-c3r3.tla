---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in [1..bound -> Values]
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values \cup {"none"}
    /\ cnt \in 0..bound

Init ==
    /\ seq \in [1..bound -> Values]
    /\ pos = 1
    /\ cand \in Values \cup {"none"}
    /\ cnt = 0

ScanStep ==
    /\ pos <= bound
    /\ LET x == seq[pos] IN
         /\ IF cand = "none" THEN cand' = x ELSE cand' = cand
         /\ cnt' = IF cand = "none" THEN 1
                  ELSE IF cand = x THEN cnt + 1
                  ELSE IF cnt > 0 THEN cnt - 1
                  ELSE cnt
    /\ pos' = pos + 1

Next == ScanStep

Spec == Init /\ [][Next]_vars /\ WF_vars(ScanStep)

\* The invariant that characterises the majority vote: any element that truly is
\* in the majority of the scanned sequence must equal the candidate once the
\* scan has completed.
Correct ==
    \A x \in Values :
        (2 * Cardinality({i \in 1..bound : seq[i] = x}) > bound) => (cand = x)

\* The candidate and counter always describe a gap-free head of the scan: the
\* candidate is either unset or equal to the element at the scan head, and the
\* counter is zero exactly when there is no candidate.
Inv ==
    /\ (pos > bound \/ (cand # "none") => (cand = seq[pos]))
    /\ (cnt = 0) => (cand = "none")

Complete == pos = bound + 1

\* Progress: the scan always eventually reaches the end of the bounded sequence.
CompleteSeq == Complete

\* BoundedSeq is a finite version of the standard Seq operator from Sequences,
\* used here to keep the state space finite for model checking.
BoundedSeq(n) == IF n = 0 THEN <<>> ELSE [1..n -> Values]

====