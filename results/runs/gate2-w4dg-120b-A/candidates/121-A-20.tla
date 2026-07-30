---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences

\* The algorithm below follows Booth's linear-time method for picking out, from
\* all rotations of a circular string, the lexicographically-least one: the
\* smallest shift such that the rotation it produces is minimal in the usual
\* lexicographic ordering, and among rotations that produce the same sequence
\* it is the smallest shift. The failure function is updated and consulted much
\* like KMP's, and the outer loop runs to twice the string length so the
\* doubled string is covered without needing any extra indexing gymnastics.
\* The spec uses zero-indexed sequences everywhere -- a separate "Sequences"
\* module defines them -- and the full expected set of identifiers is declared
\* here so the reference TLC config finds nothing missing.

CONSTANT CharacterSet, Nat
Sentinel == -1

VARIABLES str, strLen, fail, kmp, i, bestOff, pc
vars == <<str, strLen, fail, kmp, i, bestOff, pc>>

Strings == UNION { [1..n -> CharacterSet] : n \in Nat }

TypeInvariant ==
  /\ str \in Strings
  /\ strLen = Len(str)
  /\ fail \in [0..(2 * strLen) -> 0..(2 * strLen) \cup {Sentinel}]
  /\ kmp \in 0..(2 * strLen) \cup {Sentinel}
  /\ i \in 1..(2 * strLen)
  /\ bestOff \in 0..(strLen - 1)
  /\ pc \in {"outerCheck", "lookup", "compare", "updateBest",
             "followFail", "postCompare", "increment", "terminated"}

\* The best rotation is the smallest sequence among all rotations, and among
\* those that tie it is the smallest shift.
LessOrEqualToAllRotations ==
  /\ \A p \in 0..(strLen - 1) :
       \A k \in 0..(strLen - 1) :
         LET substr(a, b) == IF b >= a THEN SubSeq(str, a + 1, b + 1) ELSE @
         IN substr(bestOff, p) <= substr(p, bestOff)
  /\ \A p \in 0..(strLen - 1) :
       (substr(bestOff, p) = substr(p, bestOff)) => (bestOff <= p)

Init ==
  /\ str \in Strings
  /\ strLen = Len(str)
  /\ fail = [x \in 0..(2 * strLen) |-> Sentinel]
  /\ kmp = Sentinel
  /\ i = 1
  /\ bestOff = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ i < 2 * strLen
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, strLen, fail, kmp, i, bestOff>>

Terminate ==
  /\ pc = "outerCheck"
  /\ i >= 2 * strLen
  /\ pc' = "terminated"
  /\ UNCHANGED <<str, strLen, fail, kmp, i, bestOff>>

Lookup ==
  /\ pc = "lookup"
  /\ kmp' = fail[(i - bestOff) % (2 * strLen)]
  /\ pc' = "compare"
  /\ UNCHANGED <<str, strLen, fail, i, bestOff>>

Compare ==
  /\ pc = "compare"
  /\ (str[(i % strLen) + 1] # str[(bestOff + kmp) % strLen + 1])
  /\ kmp # Sentinel
  /\ pc' = "compare"
  /\ UNCHANGED <<str, strLen, fail, kmp, i, bestOff>>

UpdateBest ==
  /\ pc = "compare"
  /\ (str[(i % strLen) + 1] # str[(bestOff + kmp) % strLen + 1])
  /\ kmp # Sentinel
  /\ str[(i % strLen) + 1] < str[(bestOff + kmp) % strLen + 1]
  /\ bestOff' = i % strLen
  /\ pc' = "followFail"
  /\ UNCHANGED <<str, strLen, fail, kmp, i>>

FollowFail ==
  /\ pc = "followFail"
  /\ kmp' = fail[(i - bestOff) % (2 * strLen)]
  /\ pc' = "compare"
  /\ UNCHANGED <<str, strLen, fail, i, bestOff>>

PostCompare ==
  /\ pc = "compare"
  /\ (str[(i % strLen) + 1] # str[(bestOff + kmp) % strLen + 1])
  /\ kmp = Sentinel
  /\ LET cand == IF str[(i % strLen) + 1] < str[(bestOff + kmp) % strLen + 1]
                THEN i % strLen ELSE bestOff
       val == IF kmp = Sentinel THEN Sentinel ELSE kmp + 1
  IN /\ bestOff' = cand
     /\ fail' = [fail EXCEPT ![i] = val]
  /\ pc' = "increment"
  /\ UNCHANGED <<str, strLen, kmp, i>>

Increment ==
  /\ pc = "compare"
  /\ i < 2 * strLen
  /\ i' = i + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<str, strLen, fail, kmp, bestOff>>

Stall ==
  /\ pc = "terminated"
  /\ UNCHANGED vars

Next == OuterCheck \/ Terminate \/ Lookup \/ Compare \/ UpdateBest
        \/ FollowFail \/ PostCompare \/ Increment \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment) /\ WF_vars(Lookup)

Properties ==
  /\ TypeInvariant
  /\ LessOrEqualToAllRotations
  /\ (\A p \in 0..(strLen - 1) :
        SubSeq(str, bestOff + 1, strLen) ^ SubSeq(str, 1, bestOff) <=
          SubSeq(str, p + 1, strLen) ^ SubSeq(str, 1, p))
  /\ (\A p \in 0..(strLen - 1) :
        (SubSeq(str, bestOff + 1, strLen) ^ SubSeq(str, 1, bestOff) =
          SubSeq(str, p + 1, strLen) ^ SubSeq(str, 1, p)) => bestOff <= p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Lookup) /\ WF_vars(Increment) /\ WF_vars(FollowFail)
        /\ WF_vars(PostCompare)
====