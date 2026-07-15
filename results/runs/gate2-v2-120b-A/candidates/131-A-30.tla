---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

VARIABLES seq, index, cand, cnt

(*-----------------------------------------------------------------
  We re‑declare the constants and variables that are already present
  in the underlying majority‑vote specification.  No new state
  variables are introduced.
-----------------------------------------------------------------*)

(*-----------------------------------------------------------------
  Helper function: the number of occurrences of a value v in the
  prefix of seq up to but not including position i.
-----------------------------------------------------------------*)
Occurrences(v, i) ==
  Cardinality({j \in 0..(i-1) : seq[j] = v})

(*-----------------------------------------------------------------
  Type correctness invariant (the type of every variable is as
  required).  This is the same invariant that the main spec proves,
  reproduced here for completeness.
-----------------------------------------------------------------*)
TypeOK ==
  /\ seq \in Seq(Value)
  /\ index \in Nat
  /\ cand \in Value
  /\ cnt \in Nat

(*-----------------------------------------------------------------
  Safety invariant: after the whole input has been scanned, any value
  that appears more than half the time must be the candidate.
-----------------------------------------------------------------*)
Inv ==
  /\ index = Len(seq)
  /\ \A v \in Value :
        (Occurrences(v, Len(seq)) > Len(seq) / 2) => v = cand

(*-----------------------------------------------------------------
  Safety invariant required by the configuration: the same invariant
  as Inv, but we expose it under the name Correct.
-----------------------------------------------------------------*)
Correct == Inv

(*-----------------------------------------------------------------
  The initial state of the algorithm.
-----------------------------------------------------------------*)
Init ==
  /\ seq \in Seq(Value)          \* nondeterministically chosen input sequence
  /\ index = 0
  /\ cand \in Value
  /\ cnt = 0

(*-----------------------------------------------------------------
  The transition relation, exactly as in the original Boyer‑Moore
  algorithm.
-----------------------------------------------------------------*)
Next ==
  \/ /\ index < Len(seq)
        /\ LET cur == seq[index] IN
           IF cnt = 0 THEN
              /\ cand' = cur
              /\ cnt'  = 1
           ELSE
              IF cand = cur THEN
                 /\ cand' = cand
                 /\ cnt'  = cnt + 1
              ELSE
                 /\ cand' = cand
                 /\ cnt'  = cnt - 1
        /\ index' = index + 1
        /\ UNCHANGED <<seq>>
  \/ /\ index = Len(seq)
        /\ UNCHANGED <<seq, index, cand, cnt>>

(*-----------------------------------------------------------------
  The overall specification: initialization followed by zero or more
  steps of the transition relation.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, index, cand, cnt>>

=============================================================================