---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CharacterSet

\* A finite version of Nat for model checking; the .cfg replaces the Nat name
\* used in other modules with this bounded, finite set.
ZSequences == {0, 1}

\* The entire state space is finite, so every reachable state is a leaf of the
\* transition tree and bounded-model checking explores it in full.
VARIABLES str, n, f, p, i, shift, pc

vars == <<str, n, f, p, i, shift, pc>>

\* A nondeterministic string over a bounded character set; the corpus of all
\* such strings up to the maximum length is a finite set.
StrSpace == [1..3 -> CharacterSet]

Sentinel == -1

TypeInvariant ==
  /\ str \in StrSpace
  /\ n = Len(str)
  /\ f \in [0..2*n -> {Sentinel} \cup (0..2*n)]
  /\ p \in {Sentinel} \cup (0..2*n)
  /\ i \in 1..(2*n+1)
  /\ shift \in 0..(n-1)
  /\ pc \in {"outer", "lookup", "inner", "update", "follow", "postcompare"}

Init ==
  /\ str \in StrSpace
  /\ n = Len(str)
  /\ f = [j \in 0..6 |-> Sentinel]
  /\ p = Sentinel
  /\ i = 1
  /\ shift = 0
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ i < 2*n
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, n, f, p, i, shift>>

Lookup ==
  /\ pc = "lookup"
  /\ p' = f[(i + shift) % n]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, n, f, i, shift>>

\* The inner comparison loop: only continues while the characters differ and
\* the failure index is not the sentinel.
InnerLoop ==
  /\ pc = "inner"
  /\ \/ /\ str[(i % n) + 1] = str[(p + shift) % n + 1]
        /\ pc' = "postcompare"
        /\ UNCHANGED <<str, n, f, p, i, shift>>
     \/ /\ p # Sentinel
        /\ str[(i % n) + 1] # str[(p + shift) % n + 1]
        /\ pc' = "update"
        /\ UNCHANGED <<str, n, f, p, i, shift>>

UpdateMin ==
  /\ pc = "update"
  /\ str[(i % n) + 1] < str[(p + shift) % n + 1]
  /\ shift' = i % n
  /\ pc' = "follow"
  /\ UNCHANGED <<str, n, f, p, i>>

\* Follow the failure chain; the loop itself computes the proper failure value.
FollowFail ==
  /\ pc = "follow"
  /\ p' = f[p]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, n, f, i, shift>>

\* The failure array is extended by one whenever two characters differ and the
\* failure index is set to a valid chain position.
PostCompare ==
  /\ pc = "postcompare"
  /\ \/ /\ str[(i % n) + 1] # str[(p + shift) % n + 1]
        /\ p = Sentinel
        /\ str[(i % n) + 1] < str[(p + shift) % n + 1]
        /\ shift' = i % n
        /\ f' = [f EXCEPT ![(i + shift) % n] = Sentinel]
        /\ UNCHANGED p
     \/ /\ str[(i % n) + 1] # str[(p + shift) % n + 1]
        /\ f' = [f EXCEPT ![(i + shift) % n] = IF p = Sentinel THEN Sentinel ELSE p+1]
        /\ UNCHANGED <<p, shift>>
  /\ pc' = "increment"
  /\ UNCHANGED <<str, n, i>>

Increment ==
  /\ pc = "increment"
  /\ i' = i + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, n, f, p, shift>>

Terminate ==
  /\ pc = "outer"
  /\ i >= 2*n
  /\ UNCHANGED vars

Stall ==
  /\ pc = "outer"
  /\ i >= 2*n
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ Lookup \/ InnerLoop \/ UpdateMin \/ FollowFail \/ PostCompare
  \/ Increment \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars

\* Lexicographic minimality of the best rotation found by the algorithm.
Correctness ==
  /\ shift' = shift
  /\ \A k \in 1..n :
       LET rotationOf(o) ==
             SELECT m \in 1..n :
               \A x \in 1..n :
                 str[((o + x - 1) % n) + 1] = str[((m + x - 1) % n) + 1]
       IN rotationOf(shift) <= rotationOf(k)

Termination == <> (pc = "outer" /\ i >= 2*n)

====