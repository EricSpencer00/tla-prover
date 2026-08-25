---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS A, B, C, bound

(* bound is a natural number *)
ASSUME bound \in Nat

(* the set of possible element values *)
V == { A, B, C }

(* a finite version of Seq limited by the bound *)
BoundedSeq == { s \in Seq(V) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

(* auxiliary definitions *)
Count(seq, v) == Cardinality({ j \in DOMAIN seq : seq[j] = v })
Done == i > Len(seq)

(* initial state *)
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in V
    /\ cnt = 0

(* one scan step of the Boyer‑Moore algorithm *)
Scan ==
    /\ ~Done
    /\ LET x == seq[i] IN
       /\ i' = i + 1
       /\ IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt' = 1
          ELSE IF cand = x THEN
            /\ cand' = cand
            /\ cnt' = cnt + 1
          ELSE
            /\ cand' = cand
            /\ cnt' = cnt - 1

(* system transition *)
Next ==
    \/ Scan
    \/ (Done /\ UNCHANGED <<seq, i, cand, cnt>>)

(* overall specification *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>> /\ WF_<<seq, i, cand, cnt>>(Next)

(* type correctness invariant *)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in V
    /\ cnt \in Nat

(* simple inductive invariant *)
Inv ==
    /\ cnt >= 0
    /\ cand \in V

(* correctness property: any true majority must equal the final candidate *)
Correct ==
    /\ Done
    /\ \A v \in V :
          (Count(seq, v) > Len(seq) \div 2) => cand = v

====