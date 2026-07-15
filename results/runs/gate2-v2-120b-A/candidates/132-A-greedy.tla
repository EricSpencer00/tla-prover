---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS A, B, C, bound, Seq

(*--------------------------------------------------------------------
  Derived constant: the set of possible element values
--------------------------------------------------------------------*)
Values == {A, B, C}

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES seq, i, cand, cnt

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
SeqSet == { s \in [1..n -> Values] : n \in 0..bound }

(*--------------------------------------------------------------------
  Initial predicate
--------------------------------------------------------------------*)
Init ==
    /\ seq \in SeqSet
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

(*--------------------------------------------------------------------
  Action definitions
--------------------------------------------------------------------*)
Scan ==
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
    /\ UNCHANGED <<seq>>

Done ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Scan \/ Done

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(*--------------------------------------------------------------------
  Invariant: type correctness
--------------------------------------------------------------------*)
TypeOK ==
    /\ seq \in SeqSet
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

(*--------------------------------------------------------------------
  Invariant: correctness of the majority vote algorithm
--------------------------------------------------------------------*)
Correct ==
    /\ i > Len(seq)               \* scan has finished
    /\ \A v \in Values :
         (Cardinality({ j \in 1..Len(seq) : seq[j] = v }) >
          Len(seq) / 2) => v = cand

(*--------------------------------------------------------------------
  Invariant: inductive invariant (same as Correct for this model)
--------------------------------------------------------------------*)
Inv == Correct

(*--------------------------------------------------------------------
  Theorem (optional, not required by the .cfg but useful for TLC)
--------------------------------------------------------------------*)
THEOREM Spec => []Inv

====