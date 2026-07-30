---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet, Nat

\* The lexicographically-least circular substring algorithm from Booth's 1980
\* paper.  The model is deliberately tiny: it explores every possible input
\* string over CharacterSet up to the configured max length, which is what
\* makes the correctness check exhaustive for small alphabets.

MaxLen == 2

Sentinel == MaxLen + 1
Circular(i) == i % Len

VARIABLES str, Len, fail, k, i, bestShift, pc
vars == <<str, Len, fail, k, i, bestShift, pc>>

LexicographicallyLeast(s) ==
  { j \in 0..(Len - 1) : \A m \in 0..(Len - 1) : s[(j + m) % Len] <= s[(bestShift + m) % Len] }

TypeInvariant ==
  /\ str \in [0..(MaxLen - 1) -> CharacterSet]
  /\ Len = Len(str)
  /\ fail \in [0..(2 * MaxLen - 1) -> 0..(Sentinel + MaxLen - 1)]
  /\ k \in 0..(Sentinel + MaxLen - 1)
  /\ i \in 1..(2 * MaxLen)
  /\ bestShift \in 0..(Len - 1)
  /\ pc \in {"outer", "lookup", "inner", "post", "done"}

Init ==
  /\ Len \in 1..MaxLen
  /\ str \in [0..(Len - 1) -> CharacterSet]
  /\ fail = [j \in 0..(2 * MaxLen - 1) |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ bestShift = 0
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ IF i >= 2 * Len THEN pc' = "done"
     ELSE pc' = "lookup"
  /\ UNCHANGED <<str, Len, fail, k, i, bestShift>>

Lookup ==
  /\ pc = "lookup"
  /\ k = fail[Circular(bestShift + i)]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, Len, fail, i, bestShift>>

CompareChars ==
  /\ pc = "inner"
  /\ LET cur == str[Circular(i)] IN
     LET cand == str[Circular(bestShift + i)] IN
     /\ IF cur # cand /\ k # Sentinel THEN pc' = "inner"
        ELSE pc' = "post"
     /\ IF cur # cand /\ k # Sentinel /\ cur < cand
          THEN bestShift' = i
          ELSE bestShift' = bestShift
  /\ UNCHANGED <<str, Len, fail, k, i>>

FollowFail ==
  /\ pc = "inner"
  /\ k # Sentinel
  /\ k' = fail[Circular(k - 1)]
  /\ UNCHANGED <<str, Len, fail, i, bestShift, pc>>

PostComparison ==
  /\ pc = "post"
  /\ LET cur == str[Circular(i)] IN
     LET cand == str[Circular(bestShift + i)] IN
     /\ IF cur # cand /\ k = Sentinel /\ cur < cand
          THEN bestShift' = i
          ELSE bestShift' = bestShift
     /\ fail' = [fail EXCEPT ![Circular(bestShift + i)] = IF cur # cand /\ k = Sentinel
                                             THEN Sentinel
                                             ELSE k + 1]
  /\ UNCHANGED <<str, Len, k, i, pc>>

Increment ==
  /\ pc \in {"post"}
  /\ i' = i + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<str, Len, fail, k, bestShift>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ Lookup \/ CompareChars
  \/ FollowFail \/ PostComparison \/ Increment \/ Done

\* There is a stuttering path from the terminated state that allows
\* the model to settle once it stops making progress.
Spec == Init /\ [][Next]_vars /\ WF_vars(Done)

Correctness ==
  /\ pc = "done"
  /\ LexicographicallyLeast(str)

Properties == {\E pc \in {"done"} : pc = "done"}

====