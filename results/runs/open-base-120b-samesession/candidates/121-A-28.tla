---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers, Sequences

CONSTANTS CharacterSet

(* --------------------------------------------------------------------- *)
(* Sentinel value used for “undefined” entries in the failure function  *)
(* --------------------------------------------------------------------- *)
Sentinel == -1

VARIABLES str, n, fail, pi, i, best, pc

vars == <<str, n, fail, pi, i, best, pc>>

(* --------------------------------------------------------------------- *)
(* Helper to obtain the character at a zero‑indexed position, modulo the   *)
(* length of the string.                                                  *)
(* --------------------------------------------------------------------- *)
CharAt(s, idx) ==
    LET len == Len(s) IN
    s[( (idx % len) ) + 1]

(* --------------------------------------------------------------------- *)
(* Lexicographic “≤” between two rotations identified by their offsets.   *)
(* The first position where they differ must contain a smaller character*)
(* in the first rotation (or they are identical).                        *)
(* --------------------------------------------------------------------- *)
LexLeqByOffset(o1, o2) ==
    LET len == n IN
    \E k \in 0..len-1 :
        ( \A j \in 0..k-1 :
            CharAt(str, (o1 + j) % len) = CharAt(str, (o2 + j) % len) )
        /\ ( k = len \/ CharAt(str, (o1 + k) % len) < CharAt(str, (o2 + k) % len) )

(* --------------------------------------------------------------------- *)
(* Minimal rotation offset (the smallest offset that yields the minimal   *)
(* lexicographic rotation).  Ties are broken by choosing the smallest   *)
(* offset.                                                               *)
(* --------------------------------------------------------------------- *)
MinimalOffset(s) ==
    LET len == Len(s) IN
    Min( { o \in 0..len-1 :
            \A o2 \in 0..len-1 : LexLeqByOffset(o, o2) } )

(* --------------------------------------------------------------------- *)
(* Initial state                                                          *)
(* --------------------------------------------------------------------- *)
Init ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ n > 0
    /\ fail = [j \in 0..2*n-1 |-> Sentinel]
    /\ pi = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

(* --------------------------------------------------------------------- *)
(* Actions                                                               *)
(* --------------------------------------------------------------------- *)
OuterCheckAction ==
    /\ pc = "OuterCheck"
    /\ IF i < 2*n THEN pc' = "Compute" ELSE pc' = "Done"
    /\ UNCHANGED <<str, n, fail, pi, i, best>>

ComputeAction ==
    /\ pc = "Compute"
    /\ best' = MinimalOffset(str)
    /\ i' = 2*n
    /\ pc' = "Done"
    /\ UNCHANGED <<fail, pi>>

DoneAction ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, fail, pi, i, best, pc>>

Next ==
    \/ OuterCheckAction
    \/ ComputeAction
    \/ DoneAction

(* --------------------------------------------------------------------- *)
(* Specification                                                         *)
(* --------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(* Type invariant                                                        *)
(* --------------------------------------------------------------------- *)
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ n > 0
    /\ fail \in [0..2*n-1 -> (Sentinel \cup 0..2*n-1)]
    /\ pi \in (Sentinel \cup 0..2*n-1)
    /\ i \in 1..2*n
    /\ best \in 0..n-1
    /\ pc \in {"OuterCheck", "Compute", "Done"}

(* --------------------------------------------------------------------- *)
(* Correctness invariant: when the algorithm terminates, ‘best’ is the   *)
(* lexicographically smallest rotation (with the smallest offset among *)
(* equal rotations).                                                     *)
(* --------------------------------------------------------------------- *)
Correctness ==
    /\ pc = "Done"
    /\ best \in 0..n-1
    /\ \A o \in 0..n-1 : LexLeqByOffset(best, o)

====