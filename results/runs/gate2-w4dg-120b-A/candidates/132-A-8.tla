---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

\* A concrete instance of the Boyer-Moore majority vote spec, with a bounded
\* sequence length (the bound is 5 in the reference configuration).
CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

\* A bounded sequence is a function from a prefix of the natural numbers, whose
\* length is kept below the fixed bound.
Sequences ==
    {s \in [1..n -> Values] : n \in 0..bound}

VARIABLES seq, pos, cand, count
vars == <<seq, pos, cand, count>>

TypeOK ==
    /\ seq \in Sequences
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ count \in 0..bound

\* The candidate is chosen nondeterministically when the scan starts.
Init ==
    /\ seq \in Sequences
    /\ pos = 1
    /\ cand \in Values
    /\ count = 0

\* The three classic Boyer-Moore cases: adopt, increment, or decrement.
Next ==
    \/ /\ pos <= bound
       /\ count = 0
       /\ cand' = seq[pos]
       /\ count' = 1
       /\ pos' = pos + 1
       /\ UNCHANGED seq
    \/ /\ pos <= bound
       /\ seq[pos] = cand
       /\ count' = count + 1
       /\ pos' = pos + 1
       /\ UNCHANGED <<seq, cand>>
    \/ /\ pos <= bound
       /\ seq[pos] # cand
       /\ count > 0
       /\ count' = count - 1
       /\ pos' = pos + 1
       /\ UNCHANGED <<seq, cand>>
    \/ /\ pos > bound
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* Correctness: a true majority must be the final candidate (or the scan
\* is incomplete, in which case the candidate is unconstrained).
Correct ==
    \A e \in Values :
        (2 * Cardinality({i \in 1..(pos - 1) : seq[i] = e}) > (pos - 1))
            => (e = cand \/ pos <= bound)

\* The Boyer-Moore scan never runs a counter to the bounded length.
Inv == count <= bound

====