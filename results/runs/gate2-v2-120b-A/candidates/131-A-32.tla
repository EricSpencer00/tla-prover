---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(*-----------------------------------------------------------------
  The Boyer-Moore majority vote algorithm specification.
  This module extends the basic algorithm with proof obligations.
-----------------------------------------------------------------*)

VARIABLES 
    arr,      \* finite sequence of Value
    i,        \* current index (1..Len(arr))
    cand,     \* current candidate of type Value
    count,    \* current counter (non‑negative Nat)
    candHistory \* sequence of the candidate after each iteration

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)

IndexSet == 1 .. Len(arr)

CandidatesAfter(j) == 
    IF j = 0 THEN {} 
    ELSE { candHistory[j] }

Occurrences(v, upto) == 
    Cardinality({ k \in 1..upto : arr[k] = v })

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)

Init ==
    /\ i = 0
    /\ count = 0
    /\ cand = IF Len(arr) = 0 THEN CHOOSE x \in Value : TRUE 
              ELSE arr[1]            \* arbitrary value if the array is empty
    /\ candHistory = << >>

(*-----------------------------------------------------------------
  One step of the algorithm
-----------------------------------------------------------------*)

Next ==
    \/ /\ i < Len(arr)
       /\ i' = i + 1
       /\ LET x == arr[i'] IN
            IF count = 0 THEN
               /\ cand' = x
               /\ count' = 1
            ELSE IF cand = x THEN
               /\ cand' = cand
               /\ count' = count + 1
            ELSE 
               /\ cand' = cand
               /\ count' = count - 1
       /\ candHistory' = Append(candHistory, cand')
    \/ /\ i = Len(arr)       \* stutter after the scan is complete
       /\ UNCHANGED <<cand, count, candHistory>>

Spec == Init /\ [][Next]_<<i, cand, count, candHistory>>

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)

TypeOK ==
    /\ i \in IndexSet \/ i = Len(arr)
    /\ count \in Nat
    /\ cand \in Value
    /\ candHistory \in Seq(Value)
    /\ Len(candHistory) = i

(*-----------------------------------------------------------------
  Main correctness invariant (Inv) – the invariant used by the
  main algorithm specification.  It states that after processing
  the first j elements, any value occurring in a strict majority
  of those elements must be the current candidate.
-----------------------------------------------------------------*)

Inv ==
    \A j \in 0..i :
        \A v \in Value :
            (Occurrences(v, j) > j / 2) => cand = v

(*-----------------------------------------------------------------
  Derived invariant stating that the final candidate, if any
  majority exists, must be the unique majority element.
-----------------------------------------------------------------*)

Correct ==
    (i = Len(arr)) => 
        \A v \in Value :
            (Occurrences(v, Len(arr)) > Len(arr) / 2) => cand = v

(*-----------------------------------------------------------------
  Provide the names required by the .cfg file.
-----------------------------------------------------------------*)

Specification == Spec
INVARIANTS == TypeOK, Correct, Inv

====