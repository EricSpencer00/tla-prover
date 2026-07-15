---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

\* -------------------------------------------------
\* Constants (instantiated by the .cfg file)
\* -------------------------------------------------
CONSTANT A, B, C, bound, Seq

\* -------------------------------------------------
\* Derived constant: the finite set of possible values
\* -------------------------------------------------
Values == {A, B, C}

\* -------------------------------------------------
\* Helper: bounded sequences over Values with length ≤ bound
\* Seq is assumed to be precisely the set of such sequences.
\* -------------------------------------------------
BoundedSeq == { s \in Seq : Len(s) <= bound }

\* -------------------------------------------------
\* State variables
\* -------------------------------------------------
VARIABLES seq, i, cand, cnt

\* -------------------------------------------------
\* Type predicate (helps readability)
\* -------------------------------------------------
SeqOk == seq \in BoundedSeq

\* -------------------------------------------------
\* Initialization
\* -------------------------------------------------
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next ==
    \/ ScanComplete
    \/ ScanStep

\* -------------------------------------------------
\* Action: scan is complete (no state change)
\* -------------------------------------------------
ScanComplete ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

\* -------------------------------------------------
\* Action: process next element when not complete
\* -------------------------------------------------
ScanStep ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
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

\* -------------------------------------------------
\* Specification (temporal formula)
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* -------------------------------------------------
\* Type correctness invariant
\* -------------------------------------------------
TypeOK ==
    /\ SeqOk
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* -------------------------------------------------
\* Main correctness invariant:
\* if a value occurs more than half the length of the
\* sequence, then after the scan (i > Len(seq)) that value
\* must equal the final candidate.
\* -------------------------------------------------
Correct ==
    /\ i > Len(seq) =>
        \A v \in Values :
            (Cardinality({ j \in 1..Len(seq) : seq[j] = v }) >
             Len(seq) / 2) => v = cand

\* -------------------------------------------------
\* Inductive invariant (captures the classic Boyer-Moore
\* invariant: after processing the prefix 1..(i-1), the
\* candidate equals the majority element of that prefix
\* if such a majority exists, otherwise cnt = 0.)
\* -------------------------------------------------
Inv ==
    /\ i \in Nat
    /\ i = 1 \/ i = Len(seq) + 1 \/ i <= Len(seq)
    /\ (cnt = 0 => 
          \A v \in Values : 
            Cardinality({ j \in 1..(i-1) : seq[j] = v }) <= (i-1)/2)
    /\ (cnt > 0 => 
          cand \in Values /\
          Cardinality({ j \in 1..(i-1) : seq[j] = cand }) > (i-1)/2)

\* -------------------------------------------------
\* Exported set of identifiers required by the .cfg
\* -------------------------------------------------
SPECIFICATION Spec
INVARIANTS TypeOK, Correct, Inv

====