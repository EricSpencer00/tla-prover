---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* --- assumptions about the constants --- *)
ASSUME DistinctVals == A # B /\ A # C /\ B # C
ASSUME BoundIsNat   == bound \in Nat

(* --- value set --- *)
Values == { A, B, C }

(* --- bounded sequence definition (replaces Seq) --- *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

(* --- state variables --- *)
VARIABLES seq, pos, cand, cnt

(* --- initial state --- *)
Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cnt = 0
  /\ cand \in Values

(* --- next-state relation (Boyer‑Moore scan) --- *)
Next ==
  \/ /\ pos <= Len(seq)
     /\ LET x == seq[pos] IN
        /\ pos' = pos + 1
        /\ UNCHANGED seq
        /\ IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt'  = 1
           ELSE IF cand = x THEN
              /\ cand' = cand
              /\ cnt'  = cnt + 1
           ELSE
              /\ cand' = cand
              /\ cnt'  = cnt - 1
  \/ /\ pos > Len(seq)
     /\ UNCHANGED <<seq, pos, cand, cnt>>

(* --- specification --- *)
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

(* --- type correctness invariant --- *)
TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

(* --- helper to count occurrences of a value --- *)
Count(v) == Cardinality({ i \in 1..Len(seq) : seq[i] = v })

(* --- correctness property: any true majority must equal the final candidate --- *)
Correct ==
  /\ pos = Len(seq) + 1
  => \A v \in Values :
        ( Count(v) > Len(seq) \div 2 => cand = v )

(* --- additional invariant (simple sanity check) --- *)
Inv == cnt >= 0

====