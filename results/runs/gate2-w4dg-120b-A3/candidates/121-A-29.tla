---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets

\* The circular substring algorithm follows Booth's 1980 linear-time method.
\* The spec is deliberately one identifier per line for the required names.
\* Parameterised by a finite character set and a bounded maximum length.
CONSTANTS CharacterSet

MaxLen == 2
Undefined == -1

VARIABLES str, n, fail, patIdx, i, best, pc

vars == <<str, n, fail, patIdx, i, best, pc>>

\* A zero-indexed sequence: a function from an index to a character.
SeqOf(k) == [j \in 0..(k - 1) |-> CHOOSE c \in CharacterSet : TRUE]

\* Rotations: the substring view starting at a given offset.
Rot(k, o) == <<str[(j + o) % n] : j \in 0..(k - 1)>>

Init ==
  /\ str \in SeqOf(MaxLen)
  /\ n = Len(str)
  /\ fail \in [0..(2 * n) -> {-1} \union (0..(2 * n))]
  /\ patIdx = Undefined
  /\ i = 1
  /\ best = 0
  /\ pc = "outer"

OuterCheck ==
  /\ pc = "outer"
  /\ i < (2 * n)
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, n, fail, patIdx, i, best>>

Lookup ==
  /\ pc = "lookup"
  /\ fail' = [fail EXCEPT ![i] = fail[(i - 1) % n]]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, n, patIdx, i, best>>

\* The inner loop walks the candidate rotation char by char.
Inner ==
  /\ pc = "inner"
  /\ IF str[i % n] # str[(best + i) % n] /\ patIdx # Undefined
       THEN pc' = "inner"
       ELSE pc' = "post"
  /\ UNCHANGED <<str, n, fail, patIdx, i, best>>

UpdateBest ==
  /\ str[i % n] < str[(best + i) % n]
  /\ best' = i % n
  /\ UNCHANGED <<str, n, fail, patIdx, i, pc>>

FollowFailure ==
  /\ patIdx' = fail[patIdx]
  /\ UNCHANGED <<str, n, fail, i, best, pc>>

Post ==
  /\ pc = "post"
  /\ IF str[i % n] # str[(best + i) % n] /\ patIdx = Undefined
       THEN IF str[i % n] < str[(best + i) % n] THEN best' = i % n ELSE UNCHANGED best
            /\ fail' = [fail EXCEPT ![i] = IF patIdx = Undefined THEN Undefined ELSE patIdx + 1]
       ELSE UNCHANGED <<best, fail>>
  /\ pc' = "advance"
  /\ UNCHANGED <<str, n, patIdx, i>>

Advance ==
  /\ pc = "advance"
  /\ i' = i + 1
  /\ pc' = "outer"
  /\ patIdx' = Undefined
  /\ UNCHANGED <<str, n, fail, best>>

Terminate ==
  /\ pc = "outer"
  /\ i >= (2 * n)
  /\ pc' = "done"
  /\ UNCHANGED <<str, n, fail, patIdx, i, best>>

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ Lookup \/ Inner \/ UpdateBest
  \/ FollowFailure \/ Post \/ Advance \/ Terminate \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(Advance) /\ WF_vars(Terminate)

TypeInvariant ==
  /\ str \in SeqOf(MaxLen)
  /\ n = Len(str)
  /\ fail \in [0..(2 * n) -> {-1} \union (0..(2 * n))]
  /\ patIdx \in {-1} \union (0..(2 * n))
  /\ i \in 1..(2 * n + 1)
  /\ best \in 0..(n - 1)
  /\ pc \in {"outer", "lookup", "inner", "post", "advance", "done"}

\* Minimality: the identified rotation is <= all others, and ties break to the
\* smallest shift value.
Correctness ==
  /\ pc = "done"
  /\ \A o \in 0..(n - 1) : Rot(n, best) <= Rot(n, o)
  /\ \A o \in 0..(n - 1) :
       (Rot(n, best) = Rot(n, o)) ~> (best <= o)

Termination == <>(pc = "done")

====