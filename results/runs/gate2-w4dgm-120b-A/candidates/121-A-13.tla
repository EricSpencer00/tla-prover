------------------------- MODULE LeastCircularSubstring -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* The input string is a zero-indexed sequence; a literal integer index is used
\* everywhere instead of the built-in 1-indexing of Sequences.
VARIABLES str, strLen, fail, patIndex, loop, bestOffset, pc

vars == << str, strLen, fail, patIndex, loop, bestOffset, pc >>

Sentinel == strLen
MaxLoop == 2 * strLen

\* The corpus: every zero-indexed sequence over the chosen character set, up to
\* the current MaximumLoop length.
Corpus == UNION { [1 .. n -> CharacterSet] : n \in 1 .. MaximumLoop }

TypeInvariant ==
  /\ str \in Corpus
  /\ strLen = Len(str)
  /\ fail \in [0 .. MaximumLoop -> 0 .. Sentinel]
  /\ patIndex \in 0 .. Sentinel
  /\ loop \in 1 .. MaximumLoop
  /\ bestOffset \in 0 .. (strLen - 1)
  /\ pc \in {"outer", "lookup", "inner", "reset", "follow", "post", "done"}

Init ==
  /\ \E s \in Corpus : str = s
  /\ strLen = Len(str)
  /\ fail = [i \in 0 .. MaximumLoop |-> Sentinel]
  /\ patIndex = Sentinel
  /\ loop = 1
  /\ bestOffset = 0
  /\ pc = "outer"

OuterLoopCheck ==
  /\ pc = "outer"
  /\ IF loop < MaximumLoop
       THEN pc' = "lookup"
       ELSE pc' = "done"
  /\ UNCHANGED << str, strLen, fail, patIndex, loop, bestOffset >>

FailureFunctionLookup ==
  /\ pc = "lookup"
  /\ fail' = [fail EXCEPT ![loop % strLen] = fail[loop % strLen]]
  /\ pc' = "inner"
  /\ UNCHANGED << str, strLen, patIndex, loop, bestOffset >>

InnerComparisonLoop ==
  /\ pc = "inner"
  /\ LET a == str[loop % strLen] IN
     LET b == str[(bestOffset + loop) % strLen] IN
       IF a # b /\ patIndex # Sentinel
         THEN pc' = "inner"
         ELSE pc' = "reset"
  /\ UNCHANGED << str, strLen, fail, patIndex, loop, bestOffset >>

UpdateBestOffsetOnLess ==
  /\ pc = "reset"
  /\ LET a == str[loop % strLen] IN
     LET b == str[(bestOffset + loop) % strLen] IN
       IF a < b /\ patIndex # Sentinel
         THEN bestOffset' = loop % strLen
         ELSE bestOffset' = bestOffset
  /\ pc' = "follow"
  /\ UNCHANGED << str, strLen, fail, patIndex, loop >>

FollowFailureFunctionChain ==
  /\ pc = "follow"
  /\ patIndex' = fail[loop % strLen]
  /\ pc' = "post"
  /\ UNCHANGED << str, strLen, fail, loop, bestOffset >>

PostComparison ==
  /\ pc = "post"
  /\ LET a == str[loop % strLen] IN
     LET b == str[(bestOffset + loop) % strLen] IN
       IF a # b /\ patIndex = Sentinel
         THEN bestOffset' = IF a < b THEN loop % strLen ELSE bestOffset
         ELSE bestOffset' = bestOffset
  /\ fail' = [fail EXCEPT ![loop % strLen] =
                 IF a # b /\ patIndex = Sentinel THEN Sentinel ELSE patIndex + 1]
  /\ pc' = "outer"
  /\ loop' = loop + 1
  /\ UNCHANGED << str, strLen, patIndex >>

DoneStutter ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoopCheck
  \/ FailureFunctionLookup
  \/ InnerComparisonLoop
  \/ UpdateBestOffsetOnLess
  \/ FollowFailureFunctionChain
  \/ PostComparison
  \/ DoneStutter

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoopCheck) /\ WF_vars(InnerComparisonLoop)

\* Correctness: the chosen offset yields a rotation no greater than any other, and
\* if two rotations compare equal, it is the smallest shift of those.
Correctness ==
  /\ \A i \in 0 .. (strLen - 1) : Rot(i) <= Rot(bestOffset)
  /\ \A i \in 0 .. (strLen - 1) : Rot(i) = Rot(bestOffset) => i >= bestOffset
  /\ Len(str) > 0
  /\ \A i \in 0 .. (strLen - 1) : Rot(i) \in CharacterSet

Rot(k) == str[(k + loop) % strLen]

Termination ==
  <>(pc = "done")

=============================================================================