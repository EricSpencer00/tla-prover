---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* A bounded version of the standard Seq operator that only builds sequences up
\* to the configured length; this finiteness is what makes exhaustive checking
\* feasible. Sequences is still extended so that Seq itself is available.
BoundedSeq(X) == {s \in Seq(X) : Len(s) <= bound}

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Next ==
  /\ \E y \in Values :
       /\ IF pos > Len(seq) THEN seq' = seq
          ELSE seq' = [seq EXCEPT ![pos] = y]
     /\ IF pos > Len(seq) THEN pos' = pos
        ELSE pos' = pos + 1
     /\ IF pos > Len(seq) THEN cand' = cand
        ELSE IF cnt = 0 THEN IF y = cand THEN cand' = cand ELSE cand' = y
        ELSE IF cnt > 0 /\ y = cand THEN cand' = cand
        ELSE cand' = cand
     /\ IF pos > Len(seq) THEN cnt' = cnt
        ELSE IF cnt = 0 THEN cnt' = 1
        ELSE IF cnt > 0 /\ y = cand THEN cnt' = cnt + 1
        ELSE cnt' = cnt - 1

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

Correct == (cnt = 0) => (cand \notin Values)
Inv == cnt >= 0

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)
====