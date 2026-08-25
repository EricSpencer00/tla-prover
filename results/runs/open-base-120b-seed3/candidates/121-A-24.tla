---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers, Sequences, ZSequences

(*-----------------------------------------------------------------
  Constants
  -----------------------------------------------------------------*)
CONSTANTS CharacterSet

(*-----------------------------------------------------------------
  Sentinel value used for “undefined” entries in the failure function
  -----------------------------------------------------------------*)
Sentinel == -1

(*-----------------------------------------------------------------
  State variables
  -----------------------------------------------------------------*)
VARIABLES str, n, fail, k, i, best, pc

(*-----------------------------------------------------------------
  Helper definitions
  -----------------------------------------------------------------*)
Idx(j) == IF n = 0 THEN 0 ELSE j % n            \* index modulo string length
FailIdx(j) == IF n = 0 THEN 0 ELSE j % (2 * n) \* index into the doubled failure array

Rot(s, off) == [j \in 0..(n-1) |-> s[ (off + j) % n ]]

LexLe(s1, s2) ==
  \A j \in 0..(n-1) :
    IF s1[j] # s2[j] THEN s1[j] < s2[j] ELSE TRUE

(*-----------------------------------------------------------------
  Type invariant
  -----------------------------------------------------------------*)
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail \in [0..(2*n-1) -> (Sentinel \cup 0..(2*n-1))]
  /\ k \in (Sentinel \cup 0..(2*n-1))
  /\ i \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in {"Check", "Lookup", "Compare", "UpdateBest", 
             "FollowFail", "PostCmp", "IncLoop", "Done", "Stutter"}

(*-----------------------------------------------------------------
  Initial state
  -----------------------------------------------------------------*)
Init ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [j \in 0..(2*n-1) |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "Check"

(*-----------------------------------------------------------------
  Algorithmic actions (one per program‑counter label)
  -----------------------------------------------------------------*)
OuterCheck ==
  /\ pc = "Check"
  /\ IF i < 2 * n THEN
       /\ pc' = "Lookup"
     ELSE
       /\ pc' = "Done"
  /\ UNCHANGED <<str, n, fail, k, i, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ k' = fail[ FailIdx(i + best) ]
  /\ pc' = "Compare"
  /\ UNCHANGED <<str, n, fail, i, best>>

Compare ==
  /\ pc = "Compare"
  /\ LET a == str[ Idx(i) ]
         b == str[ Idx(best + k + 1) ] IN
     IF a = b THEN
        /\ k' = k + 1
        /\ pc' = "Compare"
        /\ UNCHANGED <<str, n, fail, i, best>>
     ELSE
        /\ pc' = "PostCmp"
        /\ UNCHANGED <<str, n, fail, i, best>>
        /\ UNCHANGED k   \* k will be examined in PostCmp

UpdateBest ==
  (* This action is not used directly; the update is performed in PostCmp *)
  FALSE

FollowFail ==
  (* This action is not used directly; the failure‑function chain is
     realised in PostCmp as well *)
  FALSE

PostCmp ==
  /\ pc = "PostCmp"
  /\ LET a == str[ Idx(i) ]
         b == str[ Idx(best + k + 1) ] IN
     IF a # b THEN
        (* characters differ *)
        IF a < b THEN
           /\ best' = i
        ELSE
           /\ best' = best
        /\ fail' = [fail EXCEPT ![FailIdx(i + best)] = IF k = Sentinel
                                                    THEN Sentinel
                                                    ELSE k + 1]
        /\ k' = Sentinel
        /\ pc' = "IncLoop"
     ELSE
        (* a = b, should not happen here, but treat as continuation *)
        /\ best' = best
        /\ fail' = fail
        /\ k' = k
        /\ pc' = "IncLoop"

IncLoop ==
  /\ pc = "IncLoop"
  /\ i' = i + 1
  /\ pc' = "Check"
  /\ UNCHANGED <<str, n, fail, k, best>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, fail, k, i, best>>

Stutter ==
  /\ pc = "Stutter"
  /\ UNCHANGED <<str, n, fail, k, i, best, pc>>

(*-----------------------------------------------------------------
  Next-state relation
  -----------------------------------------------------------------*)
Next ==
  \/ OuterCheck
  \/ Lookup
  \/ Compare
  \/ PostCmp
  \/ IncLoop
  \/ Done
  \/ Stutter

(*-----------------------------------------------------------------
  Specification
  -----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<str, n, fail, k, i, best, pc>>

(*-----------------------------------------------------------------
  Correctness property: when the algorithm terminates, the rotation
  starting at “best” is lexicographically minimal.
  -----------------------------------------------------------------*)
Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..(n-1) : LexLe( Rot(str, best), Rot(str, off) )

(*-----------------------------------------------------------------
  The set of invariants required by the .cfg file
  -----------------------------------------------------------------*)
INVARIANTS == TypeInvariant

(*-----------------------------------------------------------------
  The properties required by the .cfg file
  -----------------------------------------------------------------*)
PROPERTIES == Correctness

====