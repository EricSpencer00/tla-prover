---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT Value

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
Values == {v \in Value : TRUE}

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
VARIABLES seq, idx, cand, cnt

(* seq is the input sequence of values, indexed from 1 to Len(seq)
   idx is the current position (1 .. Len(seq)+1) where idx = Len(seq)+1
       means the scan is finished
   cand is the current candidate value
   cnt is the current counter (non‑negative integer)
*)

(*-----------------------------------------------------------------
  Type correctness invariant (TypeOK)
-----------------------------------------------------------------*)
TypeOK == 
  /\ seq \in Seq(Values)
  /\ idx \in 1..(Len(seq) + 1)
  /\ cand \in Values
  /\ cnt \in Nat

(*-----------------------------------------------------------------
  Initial state (INIT) – choose a concrete sequence for the model
-----------------------------------------------------------------*)
InitSeq == <<>> \/ <<>> = <<>>  \* dummy to keep the expression non‑empty
Init ==
  /\ cand \in Values
  /\ cnt = 0
  /\ idx = 1
  /\ seq = InitSeq            \* the model checker will assign a concrete seq

(*-----------------------------------------------------------------
  Transition (NEXT)
-----------------------------------------------------------------*)
Next ==
  \/ /\ idx <= Len(seq)               \* still scanning
     /\ IF cnt = 0
        THEN /\ cand' = seq[idx]
             /\ cnt'  = 1
        ELSE IF seq[idx] = cand
               THEN /\ cand' = cand
                    /\ cnt'  = cnt + 1
               ELSE /\ cand' = cand
                    /\ cnt'  = cnt - 1
     /\ idx' = idx + 1
     /\ UNCHANGED seq
  \/ /\ idx = Len(seq) + 1            \* terminal self‑loop
     /\ UNCHANGED <<seq, idx, cand, cnt>>

(*-----------------------------------------------------------------
  Specification (Spec)
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, idx, cand, cnt>>

(*-----------------------------------------------------------------
  Helper definitions for the correctness proof
-----------------------------------------------------------------*)
Occur(v, i) == Cardinality({j \in 1..i : seq[j] = v})

MajorityValue == 
  {v \in Values : Occur(v, Len(seq)) > Len(seq) / 2}

StrictMajority == 
  \E v \in MajorityValue : v

(*-----------------------------------------------------------------
  Main correctness invariant (Correct)
  After the scan is finished, any strict majority element must equal the candidate.
-----------------------------------------------------------------*)
Correct ==
  (idx = Len(seq) + 1) => 
    \A v \in Values :
      (Occur(v, Len(seq)) > Len(seq) / 2) => (v = cand)

(*-----------------------------------------------------------------
  Additional invariant (Inv) – the invariant from the original algorithm
-----------------------------------------------------------------*)
Inv ==
  (idx = Len(seq) + 1) => 
    \E v \in Values :
      (cand = v) /\ (Occur(v, Len(seq)) >= \A w \in Values : Occur(w, Len(seq)))

(*-----------------------------------------------------------------
  Theorem stating that the invariants hold under Spec
-----------------------------------------------------------------*)
THEOREM SpecImpliesInv ==
  Spec => []Inv

(*=================================================================*)
\* The .cfg file will refer to the following names:
\*   SPECIFICATION == Spec
\*   INVARIANTS == TypeOK, Correct, Inv
\*   CONSTANTS == Value
\*=================================================================*)
====