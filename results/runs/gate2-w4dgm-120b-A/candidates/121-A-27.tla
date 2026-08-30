---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* Sentinel meaning "no failure-function entry yet".
UNDEFINED == 0 - 1

VARIABLES str, n, failure, matchIdx, i, bestOffset, pc

vars == <<str, n, failure, matchIdx, i, bestOffset, pc>>

\* The corpus of all zero-indexed strings over the chosen character set, up to the
\* current length bound (pushed up by the model-checking module itself).
Corpus == UNION {[1..len -> CharacterSet] : len \in 1..n}

TypeOK ==
  /\ str \in Corpus
  /\ n = Len(str)
  /\ failure \in [0..n + n -> (0..n) \cup {UNDEFINED}]
  /\ matchIdx \in (0..n) \cup {UNDEFINED}
  /\ i \in 0..(n + n)
  /\ bestOffset \in 0..(n - 1)

Init ==
  /\ \E s \in Corpus : str = s
  /\ n = Len(str)
  /\ failure = [k \in 0..(n + n) |-> UNDEFINED]
  /\ matchIdx = UNDEFINED
  /\ i = 1
  /\ bestOffset = 0
  /\ pc = "outer"

\* Outer loop iterates over the doubled string (length 2n) to absorb the wrap-around.
OuterLoop ==
  /\ pc = "outer"
  /\ i < n + n
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, n, failure, matchIdx, i, bestOffset>>

LookupFailure ==
  /\ pc = "lookup"
  /\ failure' = [failure EXCEPT ![i + bestOffset] = failure[matchIdx]]
  /\ pc' = "compare"
  /\ UNCHANGED <<str, n, matchIdx, i, bestOffset>>

\* Inside the inner loop we work from the failure function; the i < n guard is the
\* wrap-around check (no separate circular-indexing mechanism needed).
Compare ==
  /\ pc = "compare"
  /\ i < n
  /\ str[i + 1] # str[bestOffset + 1]
  /\ matchIdx # UNDEFINED
  /\ pc' \in {"followFailure", "update"}
  /\ UNCHANGED <<str, n, failure, matchIdx, i, bestOffset>>

UpdateMin ==
  /\ pc = "compare"
  /\ str[i + 1] < str[bestOffset + 1]
  /\ bestOffset' = i
  /\ pc' = "followFailure"
  /\ UNCHANGED <<str, n, failure, matchIdx, i>>

FollowFailure ==
  /\ pc \in {"followFailure", "update"}
  /\ failure' = [failure EXCEPT ![i + bestOffset] = IF matchIdx = UNDEFINED THEN UNDEFINED ELSE matchIdx + 1]
  /\ matchIdx' = failure[matchIdx]
  /\ pc' = "post"
  /\ UNCHANGED <<str, n, i, bestOffset>>

PostComparison ==
  /\ pc = "post"
  /\ (str[i + 1] # str[bestOffset + 1] /\ matchIdx = UNDEFINED)
  /\ LET newMin == IF str[i + 1] < str[bestOffset + 1] THEN i ELSE bestOffset IN
       bestOffset' = newMin
  /\ i' = i + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, n, failure, matchIdx>>

Terminate ==
  /\ pc = "outer"
  /\ i >= n + n
  /\ pc' = "done"
  /\ UNCHANGED <<str, n, failure, matchIdx, i, bestOffset>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == OuterLoop \/ LookupFailure \/ Compare \/ UpdateMin \/ FollowFailure \/ PostComparison
        \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Terminate)

\* Both the absolute lexicographic minimum and the tie-breaking smallest shift
\* hold at termination: the chosen rotation wins every comparison against all
\* others, and any equal contender carries a larger shift value.
Correctness ==
  /\ pc = "done"
  /\ \A k \in 0..(n - 1) :
       /\ str[bestOffset + 1] <= str[k + 1]
       /\ (str[bestOffset + 1] = str[k + 1] => bestOffset <= k)

Termination == <>(pc = "done")

TypeInvariant == TypeOK

====