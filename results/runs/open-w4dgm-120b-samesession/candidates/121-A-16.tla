---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

Sentinel == 0

VARIABLES input, length, failure, pattern, loop, best, pc

vars == <<input, length, failure, pattern, loop, best, pc>>

Posts == UNION { (1..(n - 1)) \X (1..n) : n \in 1..Cardinality(CharacterSet) }

TypeInvariant ==
  /\ input \in Posts
  /\ length = Len(input)
  /\ failure \in [0..2 * length -> 0..length]
  /\ pattern \in 0..length
  /\ loop \in 1..(2 * length)
  /\ best \in 0..(length - 1)
  /\ pc \in {"outer", "lookup", "compare", "follow", "post", "done"}

Init ==
  /\ \E s \in Posts : input = s
  /\ length = Len(input)
  /\ failure = [i \in 0..(2 * length) |-> Sentinel]
  /\ pattern = Sentinel
  /\ loop = 1
  /\ best = 0
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ IF loop < 2 * length THEN pc' = "lookup" ELSE pc' = "done"
  /\ UNCHANGED <<input, length, failure, pattern, loop, best>>

Lookup ==
  /\ pc = "lookup"
  /\ pattern' = failure[loop - best]
  /\ pc' = "compare"
  /\ UNCHANGED <<input, length, failure, loop, best>>

CharsDiffer ==
  LET i == loop % length
      b == (best + loop) % length
  IN /\ input[i] # input[b]
     /\ pattern # Sentinel

CompareStep ==
  /\ pc = "compare"
  /\ CharsDiffer
  /\ pattern' = failure[pattern]
  /\ UNCHANGED <<input, length, failure, loop, best, pc>>

CandidateBetter ==
  LET i == loop % length
      b == (best + loop) % length
  IN input[i] < input[b]

UpdateBest ==
  /\ best' = loop + best
  /\ UNCHANGED <<input, length, failure, pattern, loop, pc>>

NoMatchReset ==
  /\ pc = "compare"
  /\ \A i \in 0..length : failure[i] = Sentinel
  /\ UNCHANGED <<input, length, failure, pattern, loop, best, pc>>

PostCompare ==
  /\ pc = "compare"
  /\ ~CharsDiffer
  /\ LET i == loop % length
         b == (best + loop) % length
         newPattern == IF input[i] < input[b] THEN loop ELSE pattern
         fval == IF newPattern = Sentinel THEN Sentinel ELSE newPattern + 1
     IN /\ failure' = [failure EXCEPT ![loop] = fval]
        /\ pattern' = newPattern
        /\ best' = IF input[i] < input[b] THEN loop + best ELSE best
  /\ pc' = "follow"
  /\ UNCHANGED <<input, length, loop>>

FollowStep ==
  /\ pc = "follow"
  /\ loop' = loop + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<input, length, failure, pattern, best>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop
  \/ Lookup
  \/ CompareStep
  \/ UpdateBest
  \/ NoMatchReset
  \/ PostCompare
  \/ FollowStep
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Lookup) /\ WF_vars(CompareStep) /\ WF_vars(PostCompare) /\ WF_vars(FollowStep)

Correctness ==
  /\ \A t \in 0..(length - 1) : input[(best + t) % length] <= input[t]
  /\ \A t \in 0..(length - 1) : (input[(best + t) % length] = input[t]) => t >= best

Termination == <>(pc = "done")

====