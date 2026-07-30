---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet, Nat

Sentinel == 99

VARIABLES chars, n, f, p, i, best, pc
vars == << chars, n, f, p, i, best, pc >>

TypeInvariant ==
  /\ chars \in Seq(CharacterSet)
  /\ n = Len(chars)
  /\ f \in [0..(2 * n) -> 0..(2 * n) \cup {Sentinel}]
  /\ p \in 0..(2 * n) \cup {Sentinel}
  /\ i \in 1..(2 * n)
  /\ best \in 0..(n - 1)
  /\ pc \in {"outer", "lookup", "inner", "compare", "follow", "post", "inc",
              "done"}

Init ==
  /\ chars \in Seq(CharacterSet)
  /\ n = Len(chars)
  /\ f = [k \in 0..(2 * n) |-> Sentinel]
  /\ p = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "outer"

Done == pc = "done"

OuterCheck ==
  /\ pc = "outer"
  /\ i < 2 * n
  /\ pc' = "lookup"
  /\ UNCHANGED << chars, n, f, p, i, best >>

LoopExit ==
  /\ pc = "outer"
  /\ i >= 2 * n
  /\ pc' = "done"
  /\ UNCHANGED << chars, n, f, p, i, best >>

Lookup ==
  /\ pc = "lookup"
  /\ f' = [f EXCEPT ![i] = f[best + i]]
  /\ p' = f[best + i]
  /\ pc' = "inner"
  /\ UNCHANGED << chars, n, i, best >>

Inner ==
  /\ pc = "inner"
  /\ chars[(i + best) % n] # chars[(best + p) % n]
  /\ p # Sentinel
  /\ pc' = "compare"
  /\ UNCHANGED << chars, n, f, p, i, best >>

UpdateOnLess ==
  /\ pc = "compare"
  /\ chars[(i + best) % n] < chars[(best + p) % n]
  /\ best' = i % n
  /\ UNCHANGED << chars, n, f, p, i, pc >>

Follow ==
  /\ pc = "compare"
  /\ p # Sentinel
  /\ p' = f[p]
  /\ pc' = "follow"
  /\ UNCHANGED << chars, n, f, i, best >>

PostComparison ==
  /\ pc = "post"
  /\ chars[(i + best) % n] # chars[(best + p) % n]
  /\ p = Sentinel
  /\ best' = IF chars[(i + best) % n] < chars[(best + p) % n]
             THEN i % n ELSE best
  /\ f' = [f EXCEPT ![i] = IF p = Sentinel THEN Sentinel ELSE p + 1]
  /\ UNCHANGED << chars, n, p, i, pc >>

IncLoop ==
  /\ pc \in {"compare", "follow", "post"}
  /\ pc' = "inc"
  /\ UNCHANGED << chars, n, f, p, i, best >>

BackToOuter ==
  /\ pc = "inc"
  /\ i' = i + 1
  /\ pc' = "outer"
  /\ UNCHANGED << chars, n, f, p, best >>

Stall ==
  /\ Done
  /\ UNCHANGED vars

Next == OuterCheck \/ LoopExit \/ Lookup \/ Inner \/ UpdateOnLess \/ Follow
        \/ PostComparison \/ IncLoop \/ BackToOuter \/ Stall

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(OuterCheck) /\ WF_vars(Lookup) /\ WF_vars(IncLoop)
  /\ WF_vars(BackToOuter)

RotationAt(k) == SubSeq(chars, k + 1, n) \o SubSeq(chars, 1, k)

Correctness ==
  /\ best \in 0..(n - 1)
  /\ \A k \in 0..(n - 1):
        /\ RotationAt(best) <= RotationAt(k)
        /\ (RotationAt(best) = RotationAt(k) => best <= k)

Properties == Spec /\ TypeInvariant /\ Correctness
====