---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}
Seqs == UNION { (1..n) -> Values : n \in 0..bound }

VARIABLES seq, pos, cand, count

TypeOK ==
    /\ seq \in Seqs
    /\ pos \in Nat
    /\ cand \in Values
    /\ count \in 0..bound

Init ==
    /\ seq \in Seqs
    /\ pos = 1
    /\ cand \in Values
    /\ count = 0

Next ==
    \/ /\ pos <= Len(seq)
       /\ LET x == seq[pos] IN
          /\ IF cand = x /\ count < bound THEN count' = count + 1
             ELSE IF cand = x THEN cand' = x /\ count' = 1
             ELSE IF count > 0 THEN count' = count - 1
             ELSE cand' = x /\ count' = 1
          /\ UNCHANGED <<seq, pos>>
       /\ pos' = pos + 1
    \/ /\ UNCHANGED <<seq, pos, cand, count>>

Spec == Init /\ [][Next]_<<seq, pos, cand, count>>

\* A true majority must be the candidate left after a complete scan.
Correct ==
    \A e \in Values :
        (\A i \in 1..Len(seq) : seq[i] = e /\ 2 * Cardinality({j \in 1..Len(seq) : seq[j] = e}) > Len(seq))
            => e = cand

\* The usual inductive invariant.
Inv ==
    /\ pos >= 1
    /\ pos <= Len(seq) + 1
    /\ count <= Len(seq)

WeakFairness ==
    /\ WF_vars(Next)
    /\ WF_vars(\A e \in Values : Next)
    /\ WF_vars(\A e \in Values : Next)

====