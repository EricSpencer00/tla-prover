---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, ZSequences

CONSTANTS CharacterSet

\* The sentinel value means "no failure function entry / no match so far".
Sentinel == Cardinality(CharacterSet)

VARIABLES inString, n, failure, pm, outer, bestOffset, pc

vars == <<inString, n, failure, pm, outer, bestOffset, pc>>

TypeInvariant ==
  /\ inString \in [1..Cardinality(CharacterSet) -> CharacterSet]
  /\ n = Len(inString)
  /\ failure \in [0..(2 * Cardinality(CharacterSet) - 1) -> 0..Cardinality(CharacterSet)]
  /\ pm \in 0..Cardinality(CharacterSet)
  /\ outer \in 1..(2 * Cardinality(CharacterSet))
  /\ bestOffset \in 0..(n - 1)
  /\ pc \in {"outer", "lookup", "compare", "postcompare"}

Init ==
  /\ \E s \in [1..Cardinality(CharacterSet) -> CharacterSet] : inString = s
  /\ n = Len(inString)
  /\ failure = [i \in 0..(2 * Cardinality(CharacterSet) - 1) |-> Sentinel]
  /\ pm = Sentinel
  /\ outer = 1
  /\ bestOffset = 0
  /\ pc = "outer"

Rotate(s, i) == s[((i % n) + 1)]

Outer ==
  /\ pc = "outer"
  /\ outer < (2 * n)
  /\ pc' = "lookup"
  /\ UNCHANGED <<inString, n, failure, pm, outer, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ failure' = [failure EXCEPT ![outer] = failure[bestOffset]]
  /\ pm' = failure[bestOffset]
  /\ pc' = "compare"
  /\ UNCHANGED <<inString, n, outer, bestOffset>>

Compare ==
  /\ pc = "compare"
  /\ Rotate(inString, outer) # Rotate(inString, bestOffset + pm)
  /\ pm # Sentinel
  /\ pc' = "postcompare"
  /\ UNCHANGED <<inString, n, failure, pm, outer, bestOffset>>

UpdateBest ==
  /\ pc = "compare"
  /\ Rotate(inString, outer) < Rotate(inString, bestOffset + pm)
  /\ bestOffset' = outer
  /\ UNCHANGED <<inString, n, failure, pm, outer, pc>>

FollowFailure ==
  /\ pc = "compare"
  /\ pm # Sentinel
  /\ failure[pm] # Sentinel
  /\ pm' = failure[pm]
  /\ UNCHANGED <<inString, n, failure, outer, bestOffset, pc>>

Postcompare ==
  /\ pc = "postcompare"
  /\ IF Rotate(inString, outer) # Rotate(inString, bestOffset + pm)
        THEN LET newOffset == IF Rotate(inString, outer) < Rotate(inString, bestOffset + pm)
                             THEN outer ELSE bestOffset
             IN LET newFailure == IF pm = Sentinel
                                   THEN Sentinel
                                   ELSE pm + 1
                IN <<bestOffset, failure>> = <<newOffset, [failure EXCEPT ![outer] = newFailure]>>
        ELSE <<bestOffset, failure>> = <<bestOffset, failure>>
  /\ pc' = "increment"
  /\ UNCHANGED <<inString, n, pm, outer>>

Increment ==
  /\ pc = "increment"
  /\ outer' = outer + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inString, n, failure, pm, bestOffset>>

Stutter ==
  /\ pc = "increment"
  /\ outer >= (2 * n)
  /\ UNCHANGED vars

Next ==
  \/ Outer
  \/ Lookup
  \/ Compare
  \/ UpdateBest
  \/ FollowFailure
  \/ Postcompare
  \/ Increment
  \/ Stutter

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Lookup) /\ WF_vars(Compare) /\ WF_vars(UpdateBest)
        /\ WF_vars(Postcompare) /\ WF_vars(Increment)

\* The lexicographically-minimal rotation beats every other rotation.
Correctness ==
  /\ \A i \in 0..(n - 1) : Rotate(inString, bestOffset + i) >= Rotate(inString, bestOffset)
  /\ \A i \in 0..(n - 1) : (Rotate(inString, bestOffset + i) = Rotate(inString, bestOffset))
                          => (i >= bestOffset)

Termination == <>(pc = "increment" /\ outer >= (2 * n))

====