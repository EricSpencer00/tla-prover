---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT A, B, C, bound

(* The set of possible element values *)
Values == { A, B, C }

(* Finite sequences of length at most |bound| over a given set *)
BoundedSeq(V) == { s \in Seq(V) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant                                             *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

(* ---------------------------------------------------------------------- *)
(* Initial state                                                          *)
(* ---------------------------------------------------------------------- *)
Init ==
    /\ seq \in BoundedSeq(Values)
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

(* ---------------------------------------------------------------------- *)
(* Scan the next element according to the Boyer‑Moore rules               *)
(* ---------------------------------------------------------------------- *)
Scan ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
         IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt'  = 1
         ELSE IF cand = x THEN
            /\ cand' = cand
            /\ cnt'  = cnt + 1
         ELSE
            /\ cand' = cand
            /\ cnt'  = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

(* ---------------------------------------------------------------------- *)
(* No‑op when the scan is finished                                         *)
(* ---------------------------------------------------------------------- *)
Done ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Scan \/ Done

(* ---------------------------------------------------------------------- *)
(* Specification                                                          *)
(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* ---------------------------------------------------------------------- *)
(* Majority predicate                                                     *)
(* ---------------------------------------------------------------------- *)
Maj(m) ==
    /\ m \in Values
    /\ Cardinality({ j \in 1..Len(seq) : seq[j] = m }) > Len(seq) / 2

(* ---------------------------------------------------------------------- *)
(* Correctness property: any true majority must equal the final candidate *)
(* ---------------------------------------------------------------------- *)
Correct ==
    /\ i > Len(seq) => \A m \in Values : Maj(m) => m = cand

(* ---------------------------------------------------------------------- *)
(* Inductive invariant (here the same as the type invariant)            *)
(* ---------------------------------------------------------------------- *)
Inv == TypeOK

====