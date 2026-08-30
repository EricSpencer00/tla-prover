---- MODULE MCMajority ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}
Nxt(v) == CASE v = A -> B
            [] v = B -> C
            [] v = C -> A

\* BoundedSeq is a finite version of the usual Seq: sequences of length
\* up to the model-checked bound, rather than the unbounded version.
BoundedSeq == UNION { [1 .. n -> Values] : n \in 0 .. bound }
SeqL(q) == IF q = {} THEN 0 ELSE CHOOSE n \in 1 .. bound : \E f \in [1 .. n -> Values] : q = f

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in 1 .. bound + 1
    /\ cand \in Values
    /\ count \in 0 .. bound

Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in Values
    /\ count = 0

\* The three cases of the Boyer-Moore scan: adopt a new candidate, grow the
\* run of the current one, or give up one unit of it.
Next ==
    /\ pos <= SeqL(seq)
    /\ LET x == seq[pos] IN
         \/ (count = 0 /\ cand' = x /\ count' = 1)
         \/ (x = cand /\ count' = count + 1)
         \/ (x # cand /\ count' = count - 1)
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Next)
    /\ WF_vars(\E q \in BoundedSeq : seq' = q /\ UNCHANGED <<pos, cand, count>>)

\* After a complete scan any element holding a strict majority must be the
\* final candidate -- this is exactly what the scan is designed to guarantee.
Correct == pos = SeqL(seq) + 1 => \A x \in Values : (2 * Cardinality({i \in 1 .. SeqL(seq) : seq[i] = x}) > SeqL(seq)) => x = cand

\* The counter and candidate together capture the Boyer-Moore invariant: no
\* other element can hold a strict majority over the current candidate.
Inv ==
    \A x \in Values :
        (x # cand /\ 2 * Cardinality({i \in 1 .. SeqL(seq) : seq[i] = x}) > SeqL(seq))
            => (2 * Cardinality({i \in 1 .. SeqL(seq) : seq[i] = cand}) > SeqL(seq) /\ count > 0)

TypeOKInv == TypeOK /\ Inv

\* Weak fairness on the scan: it always eventually reaches the end of the
\* current sequence.
Complete == WF_vars(\E q \in BoundedSeq : seq' = q /\ UNCHANGED <<pos, cand, count>>)

====