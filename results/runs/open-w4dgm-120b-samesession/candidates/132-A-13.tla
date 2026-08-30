---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

BoundedSeq(V, n) == [i \in 1..n |-> V[[1..n] EXCEPT ![i] \in V]]
AllSeqs == UNION {BoundedSeq(Values, n) : n \in 0..bound}

TypeOK ==
    /\ seq \in AllSeqs
    /\ pos \in 1..(Len(seq) + 1)
    /\ cand \in Values
    /\ count \in 0..bound

Init ==
    /\ seq \in AllSeqs
    /\ pos = 1
    /\ cand \in Values
    /\ count = 0

Step ==
    /\ pos <= Len(seq)
    /\ \/ /\ seq[pos] = cand
          /\ count' = count + 1
          /\ cand' = cand
       \/ /\ count = 0
          /\ cand' = seq[pos]
          /\ count' = 1
       \/ /\ seq[pos] # cand
          /\ count > 0
          /\ count' = count - 1
          /\ cand' = cand
    /\ pos' = pos + 1
    /\ seq' = seq

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Correct == pos > Len(seq) => (\A v \in Values : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq)) => v = cand)

Inv == /\ pos <= Len(seq) + 1
       /\ pos >= 1
       /\ count >= 0

Complete == pos > Len(seq)
====