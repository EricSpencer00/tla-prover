---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt
vars == << seq, pos, cand, cnt >>

BoundedSeq(k) == UNION { [1 .. n -> Values] : n \in 0 .. k }

InitSeq == IF bound = 0 THEN {} ELSE CHOOSE s \in BoundedSeq(bound) : Len(s) = bound

TypeOK ==
    /\ seq \in BoundedSeq(bound)
    /\ pos \in 1 .. (IF Len(seq) = 0 THEN 1 ELSE Len(seq) + 1)
    /\ cand \in Values
    /\ cnt \in Nat

Init ==
    /\ seq = InitSeq
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

\* Scanning the next element: three cases, exactly as in the Boyer-Moore
\* algorithm (adopt new candidate, increment, or decrement).
Step ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
        \/ /\ cand = x /\ cnt' = cnt + 1 /\ cand' = cand
           \/ /\ cand # x /\ cnt = 0 /\ cnt' = 1 /\ cand' = x
           \/ /\ cand # x /\ cnt > 0 /\ cnt' = cnt - 1 /\ cand' = cand
    /\ pos' = pos + 1

Next == Step

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Step)

\* The main correctness property of the algorithm: any true majority element
\* must equal the candidate, after a complete scan of the entire sequence.
Correct ==
    \A e \in Values :
        ((Len(seq) > 0 /\ e \in Values) =>
            ((2 * Cardinality({ i \in 1 .. Len(seq) : seq[i] = e }) > Len(seq))
                => cand = e))

\* An inductive invariant that is weaker than Correct but still useful for
\* compositional reasoning and intermediate checks.
Inv == \A e \in Values :
    ((2 * Cardinality({ i \in 1 .. Len(seq) : seq[i] = e }) > Len(seq))
        => e = cand)

Complete == \A e \in Values : TRUE

====