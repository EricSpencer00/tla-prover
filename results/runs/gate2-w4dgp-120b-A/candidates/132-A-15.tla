---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Vals == {A, B, C}
Seqs == UNION { [1..n -> Vals] : n \in 0..bound }

VARIABLES seq, pos, cand, ct

TypeOK ==
    /\ seq \in Seqs
    /\ pos \in Nat
    /\ cand \in Vals
    /\ ct \in Nat

Init ==
    /\ seq \in Seqs
    /\ pos = 1
    /\ cand \in Vals
    /\ ct = 0

Step ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
        \/ (ct = 0 /\ cand' = x /\ ct' = 1)
        \/ (cand = x /\ ct' = ct + 1)
        \/ (cand # x /\ ct' = ct - 1)
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_<<seq, pos, cand, ct>>

Correct ==
    \A a \in Vals :
        (2 * (Cardinality {j \in 1..Len(seq) : seq[j] = a}) > Len(seq)) => (cand = a)

Inv == ct = Cardinality {j \in 1..pos : seq[j] = cand}

Complete == (pos > Len(seq)) ~> (pos > Len(seq))

====