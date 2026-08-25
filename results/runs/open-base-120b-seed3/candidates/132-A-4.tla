---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

(* ---------------------------------------------------------------------- *)
(* Value set of the three distinct elements                                 *)
(* ---------------------------------------------------------------------- *)
ValueSet == { A, B, C }

(* ---------------------------------------------------------------------- *)
(* Bounded sequences over a set S, length at most `bound`                    *)
(* ---------------------------------------------------------------------- *)
BoundedSeq(S) == { s : \E n \in 0..bound : s \in [1..n -> S] }

(* ---------------------------------------------------------------------- *)
(* Length of a (possibly empty) sequence                                      *)
(* ---------------------------------------------------------------------- *)
Len(s) == IF DOMAIN s = {} THEN 0 ELSE Max(DOMAIN s)

(* ---------------------------------------------------------------------- *)
(* Number of occurrences of v in sequence s                                 *)
(* ---------------------------------------------------------------------- *)
Count(s, v) == Cardinality({ i \in DOMAIN s : s[i] = v })

(* ---------------------------------------------------------------------- *)
(* State variables                                                          *)
(* ---------------------------------------------------------------------- *)
VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

(* ---------------------------------------------------------------------- *)
(* Initial state                                                            *)
(* ---------------------------------------------------------------------- *)
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos = 1
    /\ cnt = 0
    /\ cand \in ValueSet

(* ---------------------------------------------------------------------- *)
(* Next-state relation                                                      *)
(* ---------------------------------------------------------------------- *)
Next ==
    \/ /\ pos <= Len(seq)
       /\ LET x == seq[pos] IN
            IF cnt = 0 THEN
                /\ cand' = x
                /\ cnt' = 1
            ELSE IF cand = x THEN
                /\ cand' = cand
                /\ cnt' = cnt + 1
            ELSE
                /\ cand' = cand
                /\ cnt' = cnt - 1
       /\ pos' = pos + 1
       /\ UNCHANGED seq
    \/ /\ pos > Len(seq)
       /\ UNCHANGED <<seq, pos, cand, cnt>>

(* ---------------------------------------------------------------------- *)
(* Specification                                                            *)
(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* Invariants                                                               *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos \in Nat
    /\ cnt \in Nat
    /\ cand \in ValueSet

Inv ==
    /\ cnt >= 0
    /\ (cnt = 0 => cand \in ValueSet)

Correct ==
    /\ pos > Len(seq)
    /\ \A v \in ValueSet :
          (Count(seq, v) > Len(seq) / 2) => v = cand

====