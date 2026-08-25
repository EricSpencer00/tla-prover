---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(*--------------------------------------------------------------------
  CONSTANTS
--------------------------------------------------------------------*)
CONSTANTS CharacterSet

(*--------------------------------------------------------------------
  FINITE version of Nat for ZSequences replacement (right side operator)
--------------------------------------------------------------------*)
\* CharacterSet is already declared as a constant; we also define a
\* finite version of Nat to be used where needed.
\* In models the value of CharacterSet will be constrained to a finite
\* subset of Nat (e.g., 0..9).  Here we provide a default definition that
\* can be overridden by the .cfg file.
CharacterSet == 0..9

(*--------------------------------------------------------------------
  PARAMETERS
--------------------------------------------------------------------*)
SENTINEL == -1

PCSet == {"OuterCheck", "Lookup", "InnerLoop", "UpdateBest", "FollowFail",
          "PostComp", "Inc", "Done"}

(*--------------------------------------------------------------------
  STATE VARIABLES
--------------------------------------------------------------------*)
VARIABLES str, n, fail, k, i, best, pc

vars == <<str, n, fail, k, i, best, pc>>

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Idx(p) == p % n          \* modulo indexing for circular string

Rot(off) == [j \in 0..n-1 |-> str[ (off + j) % n ]]

LexLe(s, t) ==
  \E k \in 0..n-1 :
    /\ \A j \in 0..k-1 : Rot(s)[j] = Rot(t)[j]
    /\ Rot(s)[k] <= Rot(t)[k]

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail = [p \in 0..2*n |-> SENTINEL]
  /\ k = SENTINEL
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n
        THEN /\ pc' = "Lookup"
             /\ UNCHANGED <<str, n, fail, k, i, best>>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED <<str, n, fail, k, i, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ k' = fail[i]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, fail, i, best>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ let c1 == str[Idx(i)] in
     let c2 == str[Idx(best + i)] in
     IF c1 = c2
        THEN /\ pc' = "Inc"               \* characters equal, go to increment
             /\ UNCHANGED <<str, n, fail, k, i, best>>
        ELSE IF k # SENTINEL
                THEN /\ pc' = "UpdateBest"   \* continue inner loop via failure chain
                     /\ UNCHANGED <<str, n, fail, i, best>>
                ELSE /\ pc' = "PostComp"     \* no failure to follow
                     /\ UNCHANGED <<str, n, fail, i, best>>

UpdateBest ==
  /\ pc = "UpdateBest"
  /\ let c1 == str[Idx(i)] in
     let c2 == str[Idx(best + i)] in
     IF c1 < c2
        THEN /\ best' = i
        ELSE /\ UNCHANGED best
  /\ k' = fail[i]          \* follow failure function
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, fail, i>>

PostComp ==
  /\ pc = "PostComp"
  /\ let c1 == str[Idx(i)] in
     let c2 == str[Idx(best + i)] in
     IF c1 # c2
        THEN /\ IF c1 < c2 THEN best' = i ELSE UNCHANGED best
        ELSE UNCHANGED best
  /\ fail' = [fail EXCEPT ![i] = IF k = SENTINEL THEN SENTINEL ELSE k + 1]
  /\ pc' = "Inc"
  /\ UNCHANGED <<str, n, k, i>>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, fail, k, best>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ UpdateBest
  \/ PostComp
  \/ Inc
  \/ Done

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..2*n -> (0..2*n) \cup {SENTINEL}]
  /\ k \in (0..2*n) \cup {SENTINEL}
  /\ i \in 1..2*n
  /\ best \in 0..n-1
  /\ pc \in PCSet

Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..n-1 : LexLe(best, off)

====