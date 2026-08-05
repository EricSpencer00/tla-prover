---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets, Tuples

(* Utility module: defines the finite character set to use for model checking. *)
CONSTANTS CharacterSet

(* The algorithm works over zero-indexed sequences, so indices run from 0 to Len-1. *)
VARIABLES input, length, failure, pattern, loopCounter, bestOffset, pc

vars == << input, length, failure, pattern, loopCounter, bestOffset, pc >>

Sentinel == -1

TypeInvariant ==
  /\ input \in [ 1 .. length -> CharacterSet ]
  /\ length \in 0 .. 4
  /\ failure \in [ 0 .. 2 * length - 1 -> {-1} \cup (0 .. 2 * length - 1) ]
  /\ pattern \in {-1} \cup (0 .. 2 * length - 1)
  /\ loopCounter \in 0 .. 2 * length
  /\ bestOffset \in 0 .. (IF length = 0 THEN 0 ELSE length - 1)
  /\ pc \in {0, 1, 2, 3, 4, 5, 6, 7}

Init ==
  /\ input \in [ 1 .. 4 -> CharacterSet ]
  /\ length = Len(input)
  /\ failure = [ i \in 0 .. 7 |-> Sentinel ]
  /\ pattern = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = 0

OuterCheck ==
  /\ pc = 0
  /\ IF loopCounter < 2 * length
       THEN pc' = 1
       ELSE pc' = 7
  /\ UNCHANGED << input, length, failure, pattern, loopCounter, bestOffset >>

FailureLookup ==
  /\ pc = 1
  /\ pattern' = failure[loopCounter - bestOffset]
  /\ pc' = 2
  /\ UNCHANGED << input, length, failure, loopCounter, bestOffset >>

InnerLoop ==
  /\ pc = 2
  /\ pattern # Sentinel
  /\ input[loopCounter + 1] # input[pattern + 1]
  /\ pc' = 3
  /\ UNCHANGED << input, length, failure, pattern, loopCounter, bestOffset >>

UpdateBestInside ==
  /\ pc = 3
  /\ input[loopCounter + 1] < input[pattern + 1]
  /\ bestOffset' = loopCounter
  /\ pc' = 4
  /\ UNCHANGED << input, length, failure, pattern, loopCounter >>

PatternFollow ==
  /\ pc = 4
  /\ pattern' = failure[pattern]
  /\ pc' = 5
  /\ UNCHANGED << input, length, failure, loopCounter, bestOffset >>

PostComparison ==
  /\ pc = 5
  /\ input[loopCounter + 1] # input[pattern + 1]
  /\ pattern = Sentinel
  /\ IF input[loopCounter + 1] < input[pattern + 1]
       THEN bestOffset' = loopCounter
       ELSE bestOffset' = bestOffset
  /\ failure' = [ failure EXCEPT ![loopCounter - bestOffset] = IF input[loopCounter + 1] # input[pattern + 1] THEN Sentinel ELSE pattern + 1 ]
  /\ pc' = 6
  /\ UNCHANGED << input, length, pattern, loopCounter >>

IncrementLoop ==
  /\ pc = 6
  /\ loopCounter' = loopCounter + 1
  /\ pc' = 0
  /\ UNCHANGED << input, length, failure, pattern, bestOffset >>

Terminate ==
  /\ pc = 7
  /\ UNCHANGED vars

Stall ==
  /\ pc = 7
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ FailureLookup
  \/ InnerLoop
  \/ UpdateBestInside
  \/ PatternFollow
  \/ PostComparison
  \/ IncrementLoop
  \/ Terminate
  \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(FailureLookup) /\ WF_vars(IncrementLoop)

(* The best rotation offset must label the lexicographically-minimum rotation. *)
Correctness ==
  /\ bestOffset \in 0 .. (IF length = 0 THEN 0 ELSE length - 1)
  /\ \A i \in 0 .. (length - 1) :
       LET offset == i + bestOffset
           rotated(k) ==
             LET pos == (k + offset) % length
             IN input[pos + 1]
       IN \A j \in 0 .. (length - 1) :
            LET pos2 == (j + i) % length
            IN rotated(j) <= input[pos2 + 1]
  /\ \A i \in 0 .. (length - 1) :
       LET offset == i + bestOffset
           rotated(k) ==
             LET pos == (k + offset) % length
             IN input[pos + 1]
       IN \A j \in 0 .. (length - 1) :
            LET pos2 == (j + i) % length
            IN rotated(j) = input[pos2 + 1] => i <= 0

Termination == <>[pc = 7]_vars

====