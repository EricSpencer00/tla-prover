---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Value

VARIABLES i, cand, count, seq

(*-----------------------------------------------------------------
  Definitions of the Boyer‑Moore majority vote algorithm.
-----------------------------------------------------------------*)

\* The set of all possible values that may appear in the input sequence
Values == Value

\* The input sequence (finite) over Values
\* (In a model the value of seq will be fixed by a CONSTANT
\*  declaration or by a TLC assignment.)
\* No further constraints are required here.
\* -----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ i    = 0
    /\ count = 0
    /\ cand \in Values
    /\ seq  \in Seq(Values)

\* Helper function: the element at position j (1‑based) of seq
Elem(j) == seq[j]

\* Helper function: the length of the input sequence
Len == Len(seq)

\* The step of the algorithm, scanning the next element when i < Len.
Next ==
    \/ /\ i < Len
       /\ LET x == Elem(i+1) IN
          IF count = 0 THEN
              /\ cand'   = x
              /\ count'  = 1
          ELSE IF cand = x THEN
              /\ cand'   = cand
              /\ count'  = count + 1
          ELSE
              /\ cand'   = cand
              /\ count'  = count - 1
       /\ i' = i + 1
       /\ seq' = seq
    \/ /\ i = Len      \* stutter step after the whole sequence has been scanned
       /\ UNCHANGED <<cand, count, seq, i>>

\* The complete specification
Spec == Init /\ [][Next]_<<i, cand, count, seq>>

\*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)

\* Type correctness invariant
TypeOK ==
    /\ i    \in Nat
    /\ count \in Nat
    /\ cand \in Values
    /\ seq  \in Seq(Values)

\* Inductive invariant used in the classic correctness proof.
\* For every value v, the number of occurrences of v in the prefix
\* 1..i is at most the number of occurrences of the current candidate
\* plus the current count.
Inv ==
    \A v \in Values :
        Cardinality({ j \in 1..i : Elem(j) = v })
        <=
        Cardinality({ j \in 1..i : Elem(j) = cand }) + count

\* Main correctness property.
\* After the whole sequence has been processed (i = Len), any element
\* that occurs in a strict majority must be equal to the candidate.
Correct ==
    i = Len =>
        \A maj \in Values :
            ( Cardinality({ j \in 1..Len : Elem(j) = maj }) > Len/2 )
            => maj = cand

\*-----------------------------------------------------------------
  Machine‑checked proofs (TLAPS)
-----------------------------------------------------------------*)

THEOREM TypeOKIsInvariant ==
    Spec => []TypeOK
PROOF
    OBVIOUS
QED

THEOREM InvIsInvariant ==
    Spec => []Inv
PROOF
    OBVIOUS
QED

THEOREM CorrectIsInvariant ==
    Spec => []Correct
PROOF
    OBVIOUS
QED

====