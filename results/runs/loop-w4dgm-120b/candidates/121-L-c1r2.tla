---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* A zero-indexed sequence of characters drawn from the finite set CharacterSet
String == UNION {[1..n -> CharacterSet] : n \in Nat}
MaxLen == 2
Sentinel == 0 - 1

VARIABLES str, n, fail, pattern, outer, best, pc

vars == <<str, n, fail, pattern, outer, best, pc>>

TypeInvariant ==
  /\ str \in String
  /\ n = Len(str)
  /\ fail \in [0..2*n -> (0..2*n) \cup {Sentinel}]
  /\ pattern \in (0..2*n) \cup {Sentinel}
  /\ outer \in 1..(2*n + 1)
  /\ best \in 0..(n - 1)
  /\ pc \in {1, 2, 3, 4, 5, 6, 7}

Init ==
  /\ \E s \in String : str = s
  /\ n = Len(str)
  /\ fail = [i \in 0..(2*n) |-> Sentinel]
  /\ pattern = Sentinel
  /\ outer = 1
  /\ best = 0
  /\ pc = 1

OuterCheck ==
  /\ pc = 1
  /\ IF outer < 2 * n
     THEN pc' = 2
     ELSE pc' = 7
  /\ UNCHANGED <<str, n, fail, pattern, outer, best>>

FailureLookup ==
  /\ pc = 2
  /\ pattern' = fail[outer - best - 1]
  /\ pc' = 3
  /\ UNCHANGED <<str, n, fail, outer, best>>

\* The inner loop is implemented as two guarded transitions rather than a
\* single while statement, because TLA+ actions are atomic.
InnerLoopStep ==
  /\ pc = 3
  /\ LET cur == str[1 + ((outer) % n)]
         cand == str[1 + ((best + pattern + 1) % n)]
         canStep == (cur # cand) /\ pattern # Sentinel in
  /\ IF canStep
     THEN pc' = 4
     ELSE pc' = 5
  /\ UNCHANGED <<str, n, fail, pattern, outer, best>>

UpdateBestLess ==
  /\ pc = 4
  /\ LET cur == str[1 + (outer % n)]
         cand == str[1 + ((best + pattern + 1) % n)] in
       best' = IF cur < cand THEN outer ELSE best
  /\ pc' = 5
  /\ UNCHANGED <<str, n, fail, pattern, outer>>

FollowFailureLink ==
  /\ pc = 5
  /\ pattern' = IF pattern = Sentinel THEN Sentinel ELSE fail[pattern - 1]
  /\ pc' = 6
  /\ UNCHANGED <<str, n, fail, outer, best>>

\* The post-comparison step re-checks only when the failure chain is exhausted.
PostCompare ==
  /\ pc = 6
  /\ LET cur == str[1 + (outer % n)]
         cand == str[1 + ((best + pattern + 1) % n)] in
       /\ IF (cur # cand) /\ pattern = Sentinel /\ cur < cand
          THEN best' = outer
          ELSE best' = best
       /\ fail' = IF cur = cand
                 THEN [fail EXCEPT ![outer - best - 1] = Sentinel]
                 ELSE [fail EXCEPT ![outer - best - 1] = pattern + 1]
  /\ outer' = outer + 1
  /\ pc' = 1
  /\ UNCHANGED <<str, n, pattern>>

Terminate ==
  /\ pc = 7
  /\ UNCHANGED vars

Stutter ==
  /\ pc = 7
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ FailureLookup \/ InnerLoopStep
  \/ UpdateBestLess \/ FollowFailureLink \/ PostCompare
  \/ Terminate \/ Stutter

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(OuterCheck) /\ WF_vars(FailureLookup)
  /\ WF_vars(InnerLoopStep) /\ WF_vars(UpdateBestLess)
  /\ WF_vars(FollowFailureLink) /\ WF_vars(PostCompare)

\* Lexicographic ordering of rotations is expressed via the two components
\* below: (a) the rotation at `best` is not greater than any other rotation,
\* and (b) among equal rotations it has the smallest shift value.
Correctness ==
  /\ \A i \in 0..(n - 1) : \A k \in 0..(n - 1) :
       IF (k = 0 \/ (i + k <= n /\ \A j \in 0..(k - 1) : str[i + j] = str[i + j]))
       THEN \A j \in 0..(n - 1) : str[1 + ((i + j) % n)] <= str[1 + ((best + j) % n)]
       ELSE TRUE
  /\ \A i \in 0..(n - 1) : (str[i + 1] = str[best + 1]) => (i >= best)

Termination == \A i \in 1..7 : (pc = i) ~> (pc = 7)

====