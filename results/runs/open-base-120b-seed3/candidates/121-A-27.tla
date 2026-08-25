---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* ------------------------------------------------------------------------
\* Sentinel value used for “undefined” entries in the failure function.
\* ------------------------------------------------------------------------
Undefined == -1

VARIABLES str, n, f, k, i, best, pc

\* ------------------------------------------------------------------------
\* Helper definitions
\* ------------------------------------------------------------------------
CharAt(p) == str[p % n]

\* ------------------------------------------------------------------------
\* Initial state
\* ------------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ f = [j \in 0..(2*n) |-> Undefined]
  /\ k = Undefined
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ------------------------------------------------------------------------
\* Step 1: outer loop check
\* ------------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n THEN
        /\ pc' = "Lookup"
     ELSE
        /\ pc' = "Done"
  /\ UNCHANGED <<str, n, f, k, i, best>>

\* ------------------------------------------------------------------------
\* Step 2: failure‑function lookup
\* ------------------------------------------------------------------------
Lookup ==
  /\ pc = "Lookup"
  /\ idx == (best + i) % n
  /\ k' = f[idx]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, f, i, best>>

\* ------------------------------------------------------------------------
\* Step 3: inner comparison loop
\* ------------------------------------------------------------------------
InnerLoop ==
  /\ pc = "InnerLoop"
  /\ cur  == CharAt(i)
  /\ cand == IF k = Undefined THEN CharAt(best) ELSE CharAt(best + k)
  /\ IF cur = cand THEN
        /\ i' = i + 1
        /\ pc' = "OuterCheck"
        /\ UNCHANGED <<str, n, f, k, best>>
     ELSE
        /\ IF k # Undefined THEN
              /\ pc' = "FollowFailure"
           ELSE
              /\ pc' = "PostComp"
        /\ UNCHANGED <<str, n, f, i, best>>

\* ------------------------------------------------------------------------
\* Step 5: follow failure function chain
\* ------------------------------------------------------------------------
FollowFailure ==
  /\ pc = "FollowFailure"
  /\ k' = f[(best + k) % n]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, f, i, best>>

\* ------------------------------------------------------------------------
\* Step 6: post‑comparison handling
\* ------------------------------------------------------------------------
PostComp ==
  /\ pc = "PostComp"
  /\ cur  == CharAt(i)
  /\ cand == CharAt(best)
  /\ IF cur # cand THEN
        /\ IF cur < cand THEN best' = i
           ELSE best' = best
        /\ f' = [f EXCEPT ![(best + i) % n] = IF k = Undefined THEN Undefined ELSE k + 1]
        /\ pc' = "Inc"
        /\ UNCHANGED <<str, n, k, i>>
     ELSE
        /\ pc' = "Inc"
        /\ UNCHANGED <<str, n, f, k, i, best>>

\* ------------------------------------------------------------------------
\* Step 7: increment loop counter
\* ------------------------------------------------------------------------
Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, f, k, best>>

\* ------------------------------------------------------------------------
\* Stuttering after termination
\* ------------------------------------------------------------------------
Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, f, k, i, best, pc>>

\* ------------------------------------------------------------------------
\* Next‑state relation
\* ------------------------------------------------------------------------
Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ FollowFailure
  \/ PostComp
  \/ Inc
  \/ Done

\* ------------------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, f, k, i, best, pc>>

\* ------------------------------------------------------------------------
\* Type invariant
\* ------------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ f \in [0..(2*n) -> (Nat \cup {Undefined})]
  /\ (k = Undefined) \/ k \in Nat
  /\ i \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in {"OuterCheck","Lookup","InnerLoop","FollowFailure","PostComp","Inc","Done"}

\* ------------------------------------------------------------------------
\* Correctness: the rotation at “best” is lexicographically minimal
\* ------------------------------------------------------------------------
Rot(p) == <<CharAt(p + j) : j \in 0..(n-1)>>

Correctness ==
  /\ pc = "Done"
  /\ \A q \in 0..(n-1) : Rot(best) \preceq Rot(q)

\* ------------------------------------------------------------------------
\* Liveness: eventual termination
\* ------------------------------------------------------------------------
Termination == <> (pc = "Done")

====