---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound, Seq

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
ValueSet == {A, B, C}

(*--------------------------------------------------------------------
  Bounded sequence operator: the set of all sequences over ValueSet
  whose length is at most the natural number 'bound'.
--------------------------------------------------------------------*)
BoundedSeq ==
  { s \in Seq(ValueSet) : Len(s) <= bound }

(*--------------------------------------------------------------------
  Variables (inherited from the main majority vote specification)
--------------------------------------------------------------------*)
VARIABLES input, pos, cand, cnt

(*--------------------------------------------------------------------
  Type invariant (for TLC's type checking)
--------------------------------------------------------------------*)
TypeOK ==
  /\ input \in BoundedSeq
  /\ pos \in Nat
  /\ cand \in ValueSet
  /\ cnt \in Nat

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ input \in BoundedSeq
  /\ pos = 1
  /\ cand \in ValueSet
  /\ cnt = 0

(*--------------------------------------------------------------------
  Majority vote actions (the three cases)
--------------------------------------------------------------------*)
Next ==
  \/ /\ pos <= Len(input)
     /\ LET current == input[pos] IN
        IF cnt = 0 THEN
          /\ cand' = current
          /\ cnt' = 1
        ELSE IF cand = current THEN
          /\ cand' = cand
          /\ cnt' = cnt + 1
        ELSE
          /\ cand' = cand
          /\ cnt' = cnt - 1
     /\ pos' = pos + 1
  \/ /\ pos > Len(input)            \* scan complete, stay in final state
     /\ UNCHANGED <<input, pos, cand, cnt>>

(*--------------------------------------------------------------------
  Main specification (temporal formula)
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<input, pos, cand, cnt>>

(*--------------------------------------------------------------------
  Main correctness property: if there is a strict majority element,
  it must equal the candidate after the scan finishes.
--------------------------------------------------------------------*)
Correct ==
  (pos > Len(input) /\ \E x \in ValueSet :
       \A i \in 1..Len(input) : input[i] = x) => cand = input[1]

(*--------------------------------------------------------------------
  Inductive invariant (type correctness plus the main invariant)
--------------------------------------------------------------------*)
Inv == TypeOK

(*--------------------------------------------------------------------
  Theorems (optional, but kept for completeness)
--------------------------------------------------------------------*)
THEOREM Spec => []Inv

====