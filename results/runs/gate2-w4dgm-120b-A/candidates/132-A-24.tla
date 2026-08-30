---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, count
vars == <<seq, pos, cand, count>>

Sequences == {f \in [1..n -> Values] : n \in 0..bound}

Init ==
    /\ seq \in Sequences
    /\ pos = 1
    /\ cand \in Values
    /\ count = 0

Next ==
    \/ IF pos <= Len(seq) THEN
           /\ IF count = 0 THEN
                 cand' = seq[pos]
              ELSE IF seq[pos] = cand THEN cand' = cand
              ELSE cand' = cand
           /\ IF count = 0 \/ seq[pos] = cand THEN count' = count + 1
              ELSE count' = count - 1
           /\ pos' = pos + 1
       ELSE UNCHANGED <<cand, count, pos>>
    /\ seq' \in Sequences

Spec == Init /\ [][Next]_vars
    /\ \A x \in {1..bound} : WF_vars(Next)
    /\ \A x \in {1..bound} : SF_vars(Next)

TypeOK ==
    /\ seq \in Sequences
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ count \in 0..bound

Correct ==
    (pos = Len(seq) + 1 /\ count > 0) => (cand = seq[1])

Inv ==
    /\ count >= 0
    /\ pos <= Len(seq) + 1
    /\ (count = 0 => pos = 1)

BoundedSeq ==
    {f \in [1..n -> Values] : n \in 0..bound}
====