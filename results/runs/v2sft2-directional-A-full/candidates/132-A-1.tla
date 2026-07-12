---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

\* ----------------------------------------------------------------------
\* CONSTANTS
\* ----------------------------------------------------------------------
CONSTANTS A, B, C, bound

\* The set of all possible model values. It must contain exactly the three
\* constants A, B, and C. The module does not explicitly forbid other
\* constants, but the reference .cfg will restrict the values to these.
\* We create the set for use in the specification.
Values == {A, B, C}

\* ----------------------------------------------------------------------
\* Bounded sequence operator
\* ----------------------------------------------------------------------
\* Seq[n] is the set of all sequences of length n over the value set.
\* For n = 0, Seq[0] is {<>} (the empty sequence).
\* For n > 0, Seq[n] is the Cartesian product of n copies of Values.
Seq == [n \in 0..bound |-> {v \in Seq(0..bound): Cardinality(v) = n /\ \A i \in 1..n: v[i] \in Values}]

\* The overall set of allowed sequences is the union of all Seq[n] for n up to bound.
SeqSet == \E n \in 0..bound: Seq[n]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES input, pos, cand, count

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
NextSeq == [ input' |-> input, pos' |-> pos, cand' |-> cand, count' |-> count ]

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ input \in SeqSet
    /\ pos = 1
    /\ cand \in Values
    /\ count = 0

\* ----------------------------------------------------------------------
\* Actions (the classic Boyer-Moore scan)
\* ----------------------------------------------------------------------
Scan ==
    /\ pos <= Len(input)
    /\ LET x == input[pos] IN
       IF cand = x THEN
          /\ count' = count + 1
          /\ cand' = cand
          /\ pos' = pos + 1
       ELSE
          IF count = 0 THEN
             /\ cand' = x
             /\ count' = 1
             /\ pos' = pos + 1
          ELSE
             /\ cand' = cand
             /\ count' = count - 1
             /\ pos' = pos + 1
    /\ input' = input

NoChange ==
    /\ input' = input
    /\ pos' = pos
    /\ cand' = cand
    /\ count' = count

Next == Scan \/ NoChange

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<input, pos, cand, count>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (ensures all variables stay within their domains)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ input \in SeqSet
    /\ pos \in 1..(Len(input) + 1)
    /\ cand \in Values
    /\ count \in Nat

\* ----------------------------------------------------------------------
\* Correctness invariant: if there is a majority element in the input,
\* then the candidate after a full scan equals that majority element.
\* ----------------------------------------------------------------------
Correct ==
    \A majority \in Values:
        ( ( \E i \in 1..Len(input): input[i] = majority ) >
          Len(input) / 2 )
          => (pos = Len(input) + 1) /\ (cand = majority)

\* ----------------------------------------------------------------------
\* Inductive invariant combining the type correctness and correctness
\* ----------------------------------------------------------------------
Inv == TypeOK /\ Correct

====