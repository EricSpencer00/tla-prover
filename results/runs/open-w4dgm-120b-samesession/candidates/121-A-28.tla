---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

CONSTANTS CharacterSet

\* Zero-indexed sequences: a function from a domain of the form 1..n to values
\* is used as a sequence with index i corresponding to position i-1.
Sequences == {[1..n -> CharacterSet] : n \in Nat}

VARIABLES inputString, strLen, failFunc, patIdx, outer, best, pc

vars == <<inputString, strLen, failFunc, patIdx, outer, best, pc>>

TypeOK ==
  /\ inputString \in Sequences
  /\ strLen = Len(inputString)
  /\ failFunc \in [0..(2 * strLen) -> (0..strLen) \cup {"undef"}]
  /\ patIdx \in (0..strLen) \cup {"undef"}
  /\ outer \in 1..(2 * strLen)
  /\ best \in 0..(strLen - 1)
  /\ pc \in {"outerCheck", "lookup", "innerComp", "mismatchLess", "follow",
             "postComp", "increment", "ended"}

Init ==
  /\ \E s \in Sequences : inputString = s
  /\ strLen = Len(inputString)
  /\ failFunc = [i \in 0..(2 * strLen) |-> "undef"]
  /\ patIdx = "undef"
  /\ outer = 1
  /\ best = 0
  /\ pc = "outerCheck"

OuterLoopCheck ==
  /\ pc = "outerCheck"
  /\ IF outer < 2 * strLen
       THEN pc' = "lookup"
       ELSE pc' = "ended"
  /\ UNCHANGED <<inputString, strLen, failFunc, patIdx, outer, best>>

Lookup ==
  /\ pc = "lookup"
  /\ failFunc' = [failFunc EXCEPT ![outer - 1] = "undef"]
  /\ pc' = "innerComp"
  /\ UNCHANGED <<inputString, strLen, patIdx, outer, best>>

\* Compare the char at the running index against the candidate offset
CharsDiffer ==
  inputString[(outer % strLen) + 1] # inputString[((outer - best) % strLen) + 1]

InnerComp ==
  /\ pc = "innerComp"
  /\ CharsDiffer
  /\ patIdx # "undef"
  /\ pc' = "mismatchLess"
  /\ UNCHANGED <<inputString, strLen, failFunc, patIdx, outer, best>>

\* A strictly smaller char at the running index moves the best offset forward
MismatchLess ==
  /\ pc = "mismatchLess"
  /\ inputString[(outer % strLen) + 1] < inputString[((outer - best) % strLen) + 1]
  /\ best' = outer % strLen
  /\ UNCHANGED <<inputString, strLen, failFunc, patIdx, outer, pc>>

\* Follow the failure function chain, or reset if it is exhausted
Follow ==
  /\ pc = "innerComp"
  /\ CharsDiffer
  /\ patIdx = "undef"
  /\ pc' = "postComp"
  /\ UNCHANGED <<inputString, strLen, failFunc, patIdx, outer, best>>

PostComp ==
  /\ pc = "postComp"
  /\ CharsDiffer
  /\ patIdx = "undef"
  /\ IF inputString[(outer % strLen) + 1] < inputString[((outer - best) % strLen) + 1]
       THEN best' = outer % strLen
       ELSE best' = best
  /\ failFunc' = [failFunc EXCEPT ![outer - 1] = "undef"]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, patIdx, outer>>

FollowLink ==
  /\ pc = "innerComp"
  /\ CharsDiffer
  /\ patIdx # "undef"
  /\ failFunc' = [failFunc EXCEPT ![outer - 1] = patIdx]
  /\ patIdx' = failFunc[patIdx]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, outer, best>>

Increment ==
  /\ pc \in {"increment", "postComp"}
  /\ outer' = outer + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, strLen, failFunc, patIdx, best>>

Stutter ==
  /\ pc = "ended"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoopCheck
  \/ Lookup
  \/ InnerComp
  \/ MismatchLess
  \/ Follow
  \/ PostComp
  \/ FollowLink
  \/ Increment
  \/ Stutter

Spec == Init /\ [][Next]_vars

TypeInvariant == TypeOK

\* The chosen rotation is lexicographically minimal and, among equals, smallest
Correctness ==
  /\ \A shift \in 1..(strLen - 1) :
       \A i \in 0..(strLen - 1) :
         inputString[(i % strLen) + 1] <= inputString[((i + shift) % strLen) + 1]
  /\ \A shift \in 1..(strLen - 1) :
       (\A i \in 0..(strLen - 1) :
          inputString[(i % strLen) + 1] = inputString[((i + shift) % strLen) + 1])
       => best <= shift

Termination == (pc = "ended") ~> (pc = "ended")

====