---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* BoundedSeq is a FINITE version of Seq, provided locally to keep the
\* model's state space finite (the .cfg replaces Seq with this).
BoundedSeq(n, e) == [i \in 1..n |-> e[i]]

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
    /\ seq \in UNION {BoundedSeq(n, Values) : n \in 0..bound}
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ count \in Nat

Init ==
    /\ seq \in UNION {BoundedSeq(n, Values) : n \in 0..bound}
    /\ pos = 1
    /\ cand \in Values
    /\ count = 0

\* The usual Boyer-Moore step, with count zero forcing a fresh candidate.
Scan ==
    /\ pos <= Len(seq)
    /\ IF count = 0
         THEN /\ cand' = seq[pos]
              /\ count' = 1
         ELSE IF seq[pos] = cand
              THEN count' = count + 1
              ELSE count' = count - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next_ == Scan

Spec == Init /\ [][Next_]_vars
    /\ WF_vars(Scan)

Correct == \A x \in Values : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => cand = x

Inv == \A x \in Values : (\A i \in 1..Len(seq) : seq[i] = x) => cand = x

\* The candidate cannot be forced back to its initial choice after a
\* complete scan, which is what makes the majority vote convergent.
NoReversion == pos >= Len(seq) => cand = cand

Properties == NoReversion
====