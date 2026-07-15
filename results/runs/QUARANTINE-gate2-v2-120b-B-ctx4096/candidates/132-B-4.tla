---- MODULE MCMajority ---------------------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS A, B, C, bound

(* The bound must be a natural number (including 0). *)
ASSUME bound \in Nat

Value == {A, B, C}

(* Set of all sequences over Value whose length is at most bound. *)
BoundedSeq(S) == 
  { seq \in [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(* The algorithm from Majority needs to be instantiated for the concrete
   value set and the concrete bound. *)
Var == <<seq, i, cand, cnt>>

(* Initial state: empty sequence, i = 0, no candidate, count = 0. *)
Init ==
  /\ seq = {}
  /\ i   = 0
  /\ cand = {}
  /\ cnt  = 0

(* Next-step relation.  It follows the standard Boyer‑Moore majority vote
   algorithm, extended with the ability to extend the sequence by one more
   element (if the bound permits). *)
Next ==
  \/ /\ i < bound
     /\ \E v \in Value :
        /\ seq' = seq \cup {[i+1 |-> v}]
        /\ i'   = i + 1
        /\ cnt' = 
              IF cnt = 0 THEN 1
              ELSE IF v = cand THEN cnt + 1
              ELSE cnt - 1
        /\ cand' = 
              IF cnt = 0 THEN v
              ELSE cand
  \/ /\ i = bound
     /\ UNCHANGED <<seq, i, cand, cnt>>

(* The safety invariant that the external Majority module expects:
   The candidate (if any) appears at least as many times as any other element
   among the already generated part of the sequence. *)
SafeInv ==
  /\ cnt >= 0
  /\ (cnt = 0 => cand = {})
  /\ (cnt > 0 => 
        \A v \in Value :
          Cardinality({ j \in 1..i : seq[j] = cand }) >= 
          Cardinality({ j \in 1..i : seq[j] = v }))

Spec == Init /\ [][Next]_Var

====