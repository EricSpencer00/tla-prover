---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    A, B, C, bound

\* ----------------------------------------------------------------------
\* Set of possible elements
\* ----------------------------------------------------------------------
ElementSet == {A, B, C}

\* ----------------------------------------------------------------------
\* BoundedSeq replaces Seq for model checking: all sequences over S of
\* length at most bound
\* ----------------------------------------------------------------------
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    seq,    \* input sequence (function 1..Len(seq) -> ElementSet)
    i,      \* current scan position (1..Len(seq)+1)
    cand,   \* current candidate element
    cnt     \* counter (non‑negative integer)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Length of the sequence (0 when seq = <<>>)
SeqLen == Len(seq)

\* Set of indices already scanned (if any)
ProcessedIndices == { j \in 1..(i-1) : j <= SeqLen }

\* Count of element e in the processed prefix
Count(e) == Cardinality({ j \in ProcessedIndices : seq[j] = e })

\* Majority predicate for an element e
IsMajority(e) == Count(e) > SeqLen / 2

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq(ElementSet)
    /\ i \in Nat
    /\ cand \in ElementSet
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Inductive invariant (captures the relationship between cnt and the
\* processed prefix)
\* ----------------------------------------------------------------------
Inv ==
    IF cnt = 0 THEN TRUE
    ELSE
        /\ cand \in ElementSet
        /\ cnt = Count(cand) - (Cardinality(ProcessedIndices) - Count(cand))

\* ----------------------------------------------------------------------
\* Correctness property: after the scan finishes, if a majority exists,
\* the candidate equals a majority element.
\* ----------------------------------------------------------------------
Correct ==
    []( (i = SeqLen + 1) =>
        ( (\E e \in ElementSet : IsMajority(e)) =>
          (\E e \in ElementSet : cand = e /\ IsMajority(e)) ) )

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq(ElementSet)
    /\ i = 1
    /\ cnt = 0
    /\ cand \in ElementSet

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ /\ i <= SeqLen
       \* scan the next element seq[i]
       LET x == seq[i] IN
         IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt' = 1
         ELSE IF cand = x THEN
            /\ cand' = cand
            /\ cnt' = cnt + 1
         ELSE
            /\ cand' = cand
            /\ cnt' = cnt - 1
         /\ i' = i + 1
         /\ UNCHANGED seq
    \/ /\ i > SeqLen
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INVARIANTS TypeOK, Correct, Inv

====