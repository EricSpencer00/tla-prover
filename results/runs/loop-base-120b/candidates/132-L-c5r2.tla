---- MODULE MCMajority ----
EXTENDS Naturals, Integers, Reals, Sequences, FiniteSets, TLA

CONSTANTS A, B, C, bound

(* set of possible element values *)
Values == { A, B, C }

(* finite version of Seq, used for model checking *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

VARIABLES seq, pos, cand, cnt

(* ---------------------------------------------------------------------- *)
(* Helper functions *)

Count(s, v) ==
  Cardinality({ i \in 1..Len(s) : s[i] = v })

PrefixCount(s, v, p) ==
  Cardinality({ i \in 1..p : s[i] = v })

(* ---------------------------------------------------------------------- *)
(* Initialization *)

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ cnt = 0
  /\ cand \in Values

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
  /\ pos <= Len(seq)
  /\ LET v == seq[pos] IN
        IF cnt = 0 THEN
          /\ cand' = v
          /\ cnt'  = 1
        ELSE IF cand = v THEN
          /\ cand' = cand
          /\ cnt'  = cnt + 1
        ELSE
          /\ cand' = cand
          /\ cnt'  = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED <<seq>>

(* ---------------------------------------------------------------------- *)
(* Specification *)

vars == <<seq, pos, cand, cnt>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in Nat
  /\ cnt \in Nat
  /\ cand \in Values
  /\ pos <= Len(seq) + 1

Correct ==
  /\ pos > Len(seq)
  /\ \A x \in Values :
        (Count(seq, x) > Len(seq) / 2) => cand = x

Inv ==
  /\ cnt = IF pos = 1 THEN 0
          ELSE 2 * PrefixCount(seq, cand, pos - 1) - (pos - 1)

====