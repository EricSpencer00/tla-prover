---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

CONSTANTS CharacterSet

\* The algorithm is sequential (no actors); the spec models one run that walks
\* the input string twice, treating it as a doubled circular buffer. The
\* failure function is the KMP-style backtrack table that lets it run in linear
\* time. Termination is a single stable state reached after the outer loop
\* finishes; termination is not an error, so a stuttering step keeps the system
\* there.

VARIABLES str, n, failure, matchIdx, i, bestOffset, pc

vars == <<str, n, failure, matchIdx, i, bestOffset, pc>>

UNDEFINED == 0
MaxString == 3
Sentinel == 99

States == {"outer", "lookup", "inner", "after", "inc", "done"}

\* ZSequences (zero-indexed) replaces the standard Naturals in the .cfg, so
\* we keep EXTENDS Naturals but do NOT declare Nat ourselves.
\* CharacterSet is assumed a subset of Nat, and the model bounds on its size
\* and on MaxString come from the external .cfg file.
SeqDomain(k) == UNION { [1..j -> CharacterSet] : j \in 0..MaxString }

TypeOK ==
  /\ str \in SeqDomain(MaxString)
  /\ n = Len(str)
  /\ failure \in [0..(2 * n) -> 0..(2 * n) \cup {UNDEFINED}]
  /\ matchIdx \in 0..(2 * n) \cup {UNDEFINED}
  /\ i \in 0..(2 * n)
  /\ bestOffset \in 0..(n - 1)
  /\ pc \in States

Init ==
  /\ str \in SeqDomain(MaxString)
  /\ n = Len(str)
  /\ failure = [k \in 0..(2 * n) |-> UNDEFINED]
  /\ matchIdx = UNDEFINED
  /\ i = 1
  /\ bestOffset = 0
  /\ pc = "outer"

\* Compute the two characters compared by the algorithm. The modulo implements
\* the circular wrap-around on the doubled string.
Chars ==
  LET cur == str[(i % n) + 1]
      cand == str[((bestOffset + i) % n) + 1]
  IN <<cur, cand>>

Outer ==
  /\ pc = "outer"
  /\ i < 2 * n
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, n, failure, matchIdx, i, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ matchIdx' = failure[(i - 1) % n]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, n, failure, i, bestOffset>>

Inner ==
  /\ pc = "inner"
  /\ LET <<cur, cand>> == Chars
  /\ \/ (cur = cand)
     \/ (matchIdx # UNDEFINED /\ i + 1 < 2 * n /\ i' = i + 1)
     \/ (matchIdx = UNDEFINED)
  /\ (cur = cand) => pc' = "after"
  /\ (matchIdx # UNDEFINED /\ cur # cand) => pc' = "inner"
  /\ (matchIdx = UNDEFINED /\ cur # cand) => pc' = "after"
  /\ bestOffset' = IF cur # cand /\ cur < cand THEN i ELSE bestOffset
  /\ UNCHANGED <<str, n, failure, i>>

After ==
  /\ pc = "after"
  /\ LET <<cur, cand>> == Chars
  /\ IF cur # cand /\ matchIdx = UNDEFINED
     THEN bestOffset' = IF cur < cand THEN i ELSE bestOffset
     ELSE bestOffset' = bestOffset
  /\ failure' = [failure EXCEPT ![i] =
                    IF cur # cand /\ matchIdx = UNDEFINED
                    THEN UNDEFINED
                    ELSE IF matchIdx = UNDEFINED THEN i + 1
                    ELSE matchIdx + 1]
  /\ pc' = "inc"
  /\ UNCHANGED <<str, n, matchIdx, i>>

Inc ==
  /\ pc = "inc"
  /\ i' = i + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, n, failure, matchIdx, bestOffset>>

Done ==
  /\ pc = "outer"
  /\ i = 2 * n
  /\ pc' = "done"
  /\ UNCHANGED <<str, n, failure, matchIdx, i, bestOffset>>

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Outer \/ Lookup \/ Inner \/ After \/ Inc \/ Done \/ Quiesce

\* The spec entry point used by TLC: Init plus the Next relation.
Spec == Init /\ [][Next]_vars

\* Correctness: the best rotation is lexicographically minimal among all
\* rotations of the input string, and ties are broken in favor of the smallest
\* shift value.
AllRotations ==
  { <<k, <<str[(k + j) % n + 1] : j \in 0..(n - 1)>>>
      : k \in 0..(n - 1) }

SeqAt(off) == <<str[(off + j) % n + 1] : j \in 0..(n - 1)>>

Correctness ==
  /\ pc = "done"
  /\ \A k \in 0..(n - 1) : SeqAt(bestOffset) <= SeqAt(k)
  /\ \A k \in 0..(n - 1) :
       (SeqAt(bestOffset) = SeqAt(k)) => bestOffset <= k

Termination == <>(pc = "done")

====