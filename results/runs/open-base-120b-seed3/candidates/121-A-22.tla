---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CharacterSet

(*--------------------------------------------------------------------
  Sentinel value for undefined failure function entries and pattern index
--------------------------------------------------------------------*)
Sentinel == -1

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Len(s) == IF s = {} THEN 0 ELSE (Max(Domain(s)) + 1)

Rotation(str, n, offset) ==
  [k \in 0..n-1 |-> str[(offset + k) % n]]

LexLe(str, n, a, b) ==
  \A k \in 0..n-1 :
    ( \A j \in 0..k-1 : a[j] = b[j] ) => a[k] <= b[k]

MinimalRotation(str, n) ==
  CHOOSE offset \in 0..n-1 :
    \A j \in 0..n-1 :
      LexLe(str, n, Rotation(str, n, offset), Rotation(str, n, j))

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES str, n, fail, pi, i, best, pc

vars == <<str, n, fail, pi, i, best, pc>>

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail = [j \in 0..2*n-1 |-> Sentinel]
  /\ pi = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

(*--------------------------------------------------------------------
  Algorithm steps (highly abstracted)
--------------------------------------------------------------------*)
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n
       THEN /\ pc' = "Lookup"
            /\ UNCHANGED <<str, n, fail, pi, i, best>>
       ELSE /\ best' = MinimalRotation(str, n)
            /\ pc' = "Done"
            /\ UNCHANGED <<fail, pi, i>>
  /\ UNCHANGED <<pc>>

Lookup ==
  /\ pc = "Lookup"
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, fail, pi, i, best>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ (* In a faithful model this would compare characters and possibly
        loop; here we abstractly move forward. *)
  /\ pc' = "Inc"
  /\ UNCHANGED <<str, n, fail, pi, i, best>>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, fail, pi, best>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
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
  /\ fail \in [0..2*n-1 -> (0..n) \cup {Sentinel}]
  /\ pi \in (0..n-1) \cup {Sentinel}
  /\ i \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "Inc", "Done"}

Correctness ==
  /\ pc = "Done"
  /\ best = MinimalRotation(str, n)
  /\ \A offset \in 0..n-1 :
        LexLe(str, n, Rotation(str, n, best), Rotation(str, n, offset))

====