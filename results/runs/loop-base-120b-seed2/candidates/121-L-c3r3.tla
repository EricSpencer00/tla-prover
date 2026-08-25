---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* Finite character set for model checking (replace Nat from Naturals)
CharacterSet == 0..3

\* Sentinel value used in the failure function
Sentinel == -1

VARIABLES str, n, fail, i, k, best, pc

\* Helper to compute rotation of a string
Rot(s, off) ==
    << s[(off + j) % Len(s)] : j \in 0..(Len(s)-1) >>

\* Initial state
Init ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ fail = [j \in 0..(2 * n) |-> Sentinel]
    /\ i = Sentinel
    /\ k = 1
    /\ best = 0
    /\ pc = "outerCheck"

\* Outer loop check
OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF k < 2 * n
          THEN pc' = "lookup"
          ELSE pc' = "done"
    /\ UNCHANGED <<str, n, fail, i, k, best>>

\* Failure function lookup
Lookup ==
    /\ pc = "lookup"
    /\ idx == (best + k) % n
    /\ i' = fail[idx]
    /\ pc' = "inner"
    /\ UNCHANGED <<str, n, fail, k, best>>

\* Inner comparison loop
Inner ==
    /\ pc = "inner"
    /\ pos1 == k % n
    /\ pos2 == IF i = Sentinel THEN 0 ELSE (best + i) % n
    /\ IF i = Sentinel THEN
          /\ pc' = "postComp"
       ELSE IF str[pos1] = str[pos2] THEN
          /\ i' = i
          /\ pc' = "postComp"
       ELSE
          /\ i' = fail[i]
          /\ pc' = "inner"
    /\ UNCHANGED <<str, n, fail, k, best>>

\* Post‑comparison actions
PostComp ==
    /\ pc = "postComp"
    /\ pos1 == k % n
    /\ pos2 == IF i = Sentinel THEN 0 ELSE (best + i) % n
    /\ best' = IF i # Sentinel /\ str[pos1] < str[pos2] THEN pos1 ELSE best
    /\ idx == (best + k) % n
    /\ fail' = [fail EXCEPT ![idx] = IF i = Sentinel THEN Sentinel ELSE i + 1]
    /\ pc' = "inc"
    /\ UNCHANGED <<str, n, i, k>>

\* Increment outer loop counter
Inc ==
    /\ pc = "inc"
    /\ k' = k + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<str, n, fail, i, best>>

\* Stutter after termination
Done ==
    /\ pc = "done"
    /\ UNCHANGED <<str, n, fail, i, k, best>>

\* Next-state relation
Next ==
    \/ OuterCheck
    \/ Lookup
    \/ Inner
    \/ PostComp
    \/ Inc
    \/ Done

vars == <<str, n, fail, i, k, best, pc>>

\* Specification
Spec == Init /\ [][Next]_vars

\* Type invariant
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ fail \in [0..(2 * n) -> (Sentinel \cup Nat)]
    /\ i \in Sentinel \cup Nat
    /\ k \in 1..(2 * n)
    /\ best \in 0..(n - 1)
    /\ pc \in {"outerCheck", "lookup", "inner", "postComp", "inc", "done"}

\* Correctness property: upon termination, best points to a lexicographically minimal rotation
Correctness ==
    /\ pc = "done"
    /\ \A shift \in 0..(n - 1) : Rot(str, best) <= Rot(str, shift)

====