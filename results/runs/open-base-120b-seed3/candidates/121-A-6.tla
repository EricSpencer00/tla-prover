---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

(*--------------------------------------------------------------------
  Finite sentinel value used to denote "undefined" entries.
--------------------------------------------------------------------*)
Sentinel == -1

VARIABLES s, len, fail, k, i, best, pc

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Domain(i) == IF len = 0 THEN {} ELSE 0..(len-1)

Rot(offset) ==
  [j \in 0..(len-1) |-> s[(offset + j) % len]]

LexLe(a, b) ==
  \A j \in 0..(len-1) :
    ( a[j] = b[j] ) \/
    ( a[j] < b[j] /\ \A k \in 0..(j-1) : a[k] = b[k] )

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ len \in Nat
  /\ s \in [Domain(i) -> CharacterSet]
  /\ fail = [j \in 0..(2*len) |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
  \/ /\ pc = "OuterCheck"
     /\ IF i < 2*len THEN pc' = "Compare" ELSE pc' = "Done"
     /\ UNCHANGED <<s, len, fail, k, i, best>>
  \/ /\ pc = "Compare"
     /\ LET p1 == i % len
            p2 == (best + i) % len
        IN
          IF s[p1] = s[p2] THEN
             /\ UNCHANGED <<best>>
          ELSE IF s[p1] < s[p2] THEN
             /\ best' = i % len
          ELSE
             /\ UNCHANGED <<best>>
     /\ pc' = "Inc"
     /\ UNCHANGED <<s, len, fail, k, i>>
  \/ /\ pc = "Inc"
     /\ i' = i + 1
     /\ pc' = "OuterCheck"
     /\ UNCHANGED <<s, len, fail, k, best>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<s, len, fail, k, i, best, pc>>

Spec == Init /\ [][Next]_<<s, len, fail, k, i, best, pc>>

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeInvariant ==
  /\ len \in Nat
  /\ s \in [Domain(i) -> CharacterSet]
  /\ fail \in [0..(2*len) -> (Nat \cup {Sentinel})]
  /\ k \in (Nat \cup {Sentinel})
  /\ i \in Nat
  /\ best \in 0..(IF len = 0 THEN 0 ELSE len-1)
  /\ pc \in {"OuterCheck", "Compare", "Inc", "Done"}
  /\ CharacterSet \subseteq Nat   \* alphabet is a subset of Nat

(*--------------------------------------------------------------------
  Correctness property: upon termination, best gives the lexicographically
  smallest rotation.
--------------------------------------------------------------------*)
Correctness ==
  /\ pc = "Done"
  /\ \A shift \in 0..(IF len = 0 THEN 0 ELSE len-1) :
        LexLe(Rot(best), Rot(shift))

============================================================================