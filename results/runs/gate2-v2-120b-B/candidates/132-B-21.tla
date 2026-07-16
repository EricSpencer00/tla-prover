---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers

CONSTANTS A, B, C, bound

(* The bound must be a natural number (including zero). *)
ASSUME bound \in Nat

Value == {A, B, C}

(* Sequences of elements from set S whose length does not exceed the bound. *)
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(* Initialization: start with an empty sequence and the majority algorithm's
   internal state reset. *)
Init ==
    /\ seq = {}
    /\ i = 0
    /\ cand = CHOOSE x \in Value : TRUE
    /\ cnt = 0

(* One step of the majority algorithm: either advance the index or, when the
   whole sequence has been processed, keep the state unchanged. *)
Next ==
    \/ /\ i < bound
       /\ i' = i + 1
       /\ seq' = seq \cup {[i+1 |-> cand]}
       /\ IF cnt = 0
          THEN /\ cand' = cand
               /\ cnt' = 1
          ELSE /\ cand' = cand
               /\ cnt' = cnt - 1
    \/ /\ i = bound
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* The intended majority answer derived from the algorithm's state. *)
MajorityAns ==
    IF cnt = 0
       THEN CHOOSE x \in Value : TRUE
       ELSE cand

(* Safety invariant: if the algorithm reports a candidate, that candidate
   appears in the sequence more often than any other element. *)
Safe ==
    IF cnt = 0
       THEN TRUE
       ELSE
          /\ cand = MajorityAns
          /\ \A x \in Value : 
               Cardinality({ j \in DOMAIN seq : seq[j] = cand }) >=
               Cardinality({ j \in DOMAIN seq : seq[j] = x })

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

====