---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants required by the .cfg file
\* ----------------------------------------------------------------------
CONSTANT A, B, C, bound, Seq

\* ----------------------------------------------------------------------
\* Derived constant: the finite set of possible element values
\* ----------------------------------------------------------------------
Values == {A, B, C}

\* ----------------------------------------------------------------------
\* The empty sequence over Values (used for the initial state)
\* ----------------------------------------------------------------------
EmptySeq == <<>>

\* ----------------------------------------------------------------------
\* Helper: length of a sequence (since we import Sequences)
\* ----------------------------------------------------------------------
Length(s) == Len(s)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, i, cand, cnt

\* ----------------------------------------------------------------------
\* Init : choose a sequence of length 0..bound, start scanning at 1,
\*        choose an initial candidate nondeterministically, and set
\*        the counter to 0.
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in { s \in Seq : Length(s) <= bound }
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* Action: Scan the next element (i.e., the element at position i)
\* ----------------------------------------------------------------------
Scan ==
    /\ i <= Length(seq) + 1
    /\ IF i = Length(seq) + 1 THEN
          /\ i' = i
          /\ UNCHANGED <<seq, cand, cnt>>
       ELSE
          LET cur == seq[i] IN
          IF cnt = 0 THEN
              /\ cand' = cur
              /\ cnt'  = 1
          ELSE IF cur = cand THEN
              /\ cand' = cand
              /\ cnt'  = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt'  = cnt - 1
          /\ i' = i + 1
          /\ UNCHANGED seq

\* ----------------------------------------------------------------------
\* Next action (only Scan is needed)
\* ----------------------------------------------------------------------
Next == Scan

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Invariant: type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in { s \in Seq : Length(s) <= bound }
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Invariant: candidate is the majority element of the scanned prefix
\* (when the counter is positive)
\* ----------------------------------------------------------------------
Inv ==
    /\ (cnt = 0) \/ 
       ( \A v \in Values :
            /\ Count(seq, v, i - 1) >= Count(seq, cand, i - 1)
                => v = cand
       )
\* Count(s, v, k) = number of occurrences of v in the first k elements of s
Count(s, v, k) == 
    IF k = 0 THEN 0
    ELSE IF s[k] = v THEN 1 + Count(s, v, k-1)
    ELSE Count(s, v, k-1)

\* ----------------------------------------------------------------------
\* Safety property: any true majority element must equal the final candidate
\* after the scan has completed.
\* ----------------------------------------------------------------------
Correct ==
    /\ i = Length(seq) + 1
    /\ Majority(seq) => cand = Majority(seq)

\* Majority(s) returns the unique element that occurs more than half the time,
\* or NULL if none exists.
Majority(s) ==
    LET n == Length(s) IN
    IF n = 0 THEN NULL
    ELSE
        IF \E v \in Values : Count(s, v, n) > n/2
        THEN CHOOSE v \in Values : Count(s, v, n) > n/2
        ELSE NULL

\* ----------------------------------------------------------------------
\* Export the required identifiers
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INVARIANTS TypeOK, Correct, Inv
====