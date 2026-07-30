---- MODULE MCMajority ----
EXTENDS Naturals

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

SeqSet == UNION { [i \in 1 .. n |-> v[i \in 1 .. n]] : n \in 0 .. bound }

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
    /\ seq \in SeqSet
    /\ pos \in 1 .. (bound + 1)
    /\ cand \in Values
    /\ count \in 0 .. bound

Init ==
    /\ seq \in SeqSet
    /\ pos = 1
    /\ cand \in Values
    /\ count = 0

NextVal(v, cand, count) ==
    IF v # cand /\ count = 0 THEN [cand |-> v, count |-> 1]
    ELSE IF v = cand THEN [count |-> count + 1]
    ELSE [count |-> count - 1]

Step ==
    /\ pos <= bound
    /\ pos \in DOMAIN seq
    /\ LET r == NextVal(seq[pos], cand, count)
       IN /\ cand' = r.cand
          /\ count' = r.count
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Done ==
    /\ pos > bound
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars

Correct ==
    \A e \in Values :
        (2 * Cardinality({i \in 1 .. bound : i \in DOMAIN seq /\ seq[i] = e}) > bound) => e = cand

Inv == (count = 0) ~> (pos > bound)

====