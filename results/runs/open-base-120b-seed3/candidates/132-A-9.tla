---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

(* The set of possible element values *)
Values == { A, B, C }

(* All sequences over Values whose length is at most bound *)
BoundedSeq == { s \in Seq(Values) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

(* Length of the current input sequence *)
LenSeq == Len(seq)

(* Number of occurrences of v in the current sequence *)
Count(v) == Cardinality({ j \in DOMAIN seq : seq[j] = v })

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

(* ----------------------------------------------------------------------
   One step of the Boyer‑Moore scan
   ---------------------------------------------------------------------- *)
Scan ==
    /\ i <= LenSeq
    /\ LET x == seq[i] IN
       IF cnt = 0 THEN
          /\ cand' = x
          /\ cnt'  = 1
          /\ i'    = i + 1
       ELSE IF cand = x THEN
          /\ cand' = cand
          /\ cnt'  = cnt + 1
          /\ i'    = i + 1
       ELSE
          /\ cand' = cand
          /\ cnt'  = cnt - 1
          /\ i'    = i + 1
    /\ UNCHANGED seq

(* ----------------------------------------------------------------------
   Stuttering step once the scan is finished
   ---------------------------------------------------------------------- *)
Stutter ==
    /\ i > LenSeq
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Scan \/ Stutter

vars == <<seq, i, cand, cnt>>

(* ----------------------------------------------------------------------
   Specification (with weak fairness to guarantee eventual progress)
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ----------------------------------------------------------------------
   Invariants required by the .cfg file
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

Inv == TypeOK

Correct ==
    (i > LenSeq) => 
        \A v \in Values : (Count(v) > LenSeq / 2) => cand = v

====