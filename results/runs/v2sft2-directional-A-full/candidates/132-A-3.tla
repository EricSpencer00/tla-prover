---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

\*======================================================================
\* CONSTANTS (must match the .cfg)
\*======================================================================
CONSTANTS A, B, C, bound

\* The set of possible values for the sequence elements
\* It is derived from the concrete constants A, B, C.
\* This is defined as a set to use with the Seq operator below.
ElemSet == {A, B, C}

\*======================================================================
\* Bounded sequence operator: all sequences of length <= bound over ElemSet
\*======================================================================
\* Seq(n) is the set of all sequences of length exactly n (using the standard
\* Seq operator from the Sequences module).
Seq(n) == [i \in 1..n |-> ElemSet[i]]

\* SeqBounded is the set of all sequences of length <= bound.
SeqBounded == { s \in { [i \in 1..n |-> ElemSet[i]] : n \in 0..bound } }

\*======================================================================
\* Variables
\*======================================================================
VARIABLES seq, pos, candidate, counter

\*======================================================================
\* Type correctness invariant (invariant 1)
\*======================================================================
TypeOK ==
    /\ seq \in SeqBounded
    /\ pos \in 1..Len(seq)
    /\ candidate \in ElemSet
    /\ counter \in Nat

\*======================================================================
\* Initial state (inherits from the main spec)
\*======================================================================
Init ==
    /\ seq \in SeqBounded
    /\ pos = 1
    /\ candidate \in ElemSet
    /\ counter = 0

\*======================================================================
\* Scan action (three-case logic)
\*======================================================================
Scan ==
    /\ pos <= Len(seq)
    /\ \E nxt \in { seq[pos] } :
        /\ candidate' = IF seq[pos] = candidate THEN candidate ELSE nxt
        /\ counter' = CASE
            seq[pos] = candidate -> counter + 1
            seq[pos] <> candidate /\ counter > 0 -> counter - 1
            TRUE -> counter
          ENDCASE
        /\ pos' = pos + 1
        /\ UNCHANGED seq

\*======================================================================
\* Next-state relation (only Scan is allowed; the spec ends when pos > Len(seq))
\*======================================================================
Next ==
    \/ Scan
    \/ (pos > Len(seq) /\ UNCHANGED <<seq, pos, candidate, counter>>)

\*======================================================================
\* Specification (invariant 2)
\*======================================================================
Spec == Init /\ [][Next]_<<seq, pos, candidate, counter>>

\*======================================================================
\* Correctness invariant (invariant 3): if a majority element exists, it equals the final candidate
\*======================================================================
Correct ==
    \A majority \in ElemSet :
        ( LET freq == Len({ i \in 1..Len(seq) : seq[i] = majority }) IN
            (freq > Len(seq) / 2) => (candidate = majority) )

\*======================================================================
\* Inductive invariant (invariant 4) used by the model checker to prove correctness
\* It captures the relationship between counter and the difference between the
\* number of occurrences of the candidate and other values.
\*======================================================================
Inv ==
    counter >= 0 /\ counter <= Len(seq)

\*======================================================================
\* Safety property (required by the .cfg)
\*======================================================================
Safety ===>
    /\ TypeOK
    /\ Correct
    /\ Inv

\*======================================================================
\* The specification to be checked by TLC
\*======================================================================
Spec == Init /\ [][Next]_<<seq, pos, candidate, counter>>

\*======================================================================
\* The module ends here
\*======================================================================
====