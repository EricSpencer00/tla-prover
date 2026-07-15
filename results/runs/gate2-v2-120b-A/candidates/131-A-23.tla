---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value

VARIABLES cand, count, i, seq, n

(* ----------------------------------------------------------------------
   Derived definitions from the original Boyer-Moore algorithm
   ---------------------------------------------------------------------- *)

\* The finite index set of the input sequence
Index == 1..n

\* The input sequence of values (a total function from indices to values)
Seq == seq

\* Occurrence count of a value up to (and including) index j
Occur(v, j) == Cardinality({ k \in 1..j : Seq[k] = v })

\* Majority predicate for a value v
Majority(v) == Occur(v, n) > n / 2

(* ----------------------------------------------------------------------
   Initialization and transition relation
   ---------------------------------------------------------------------- *)

Init ==
    /\ i = 1
    /\ count = 0
    /\ cand \in Value
    /\ n \in Nat
    /\ seq \in [1..n -> Value]

Next ==
    /\ i <= n
    /\ IF count = 0 THEN
          /\ cand' = Seq[i]
          /\ count' = 1
       ELSE IF cand = Seq[i] THEN
          /\ cand' = cand
          /\ count' = count + 1
       ELSE
          /\ cand' = cand
          /\ count' = count - 1
    /\ i' = i + 1
    /\ UNCHANGED <<cand, count, seq, n>> \* seq and n never change

Spec == Init /\ [][Next]_<<cand, count, i, seq, n>>

(* ----------------------------------------------------------------------
   Safety properties (invariants)
   ---------------------------------------------------------------------- *)

\* Type correctness invariant
TypeOK ==
    /\ i \in Nat
    /\ count \in Nat
    /\ cand \in Value
    /\ n \in Nat
    /\ seq \in [1..n -> Value]

\* The algorithm's main correctness invariant (the candidate is the only
   possible majority element after the scan completes)
Correct ==
    (i > n) => ( \A v \in Value : Majority(v) => v = cand )

\* Alias for the inductive invariant used in the original spec
Inv == Correct

=============================================================================