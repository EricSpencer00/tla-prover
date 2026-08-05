---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

\* A zero-indexed sequence type (indexed 0..n-1 instead of the standard
\* one-indexed Naturals! sequence). The model's character set is a finite
\* subset of Nat, so a finite version of Nat is substituted for the
\* standard infinite Nat in the .cfg; we keep EXTENDS Naturals here.
CONSTANTS CharacterSet

ZeroIndexed == 1..2
MaxLength == 3
Sentinel == 0
MaxChar == 2

VARIABLES string, length, failure, patIndex, loop, best, pc

vars == <<string, length, failure, patIndex, loop, best, pc>>

SeqChars(i, s) == s[i] % (MaxChar + 1)

TypeOK ==
  /\ string \in [ZeroIndexed -> CharacterSet]
  /\ length \in 0..MaxLength
  /\ failure \in [ZeroIndexed -> {Sentinel} \cup ZeroIndexed]
  /\ patIndex \in {Sentinel} \cup ZeroIndexed
  /\ loop \in ZeroIndexed
  /\ best \in ZeroIndexed
  /\ pc \in ZeroIndexed

AllRotationsGe ==
  \A i \in ZeroIndexed :
    \/ SeqChars(best, string) < SeqChars(i, string)
    \/ (SeqChars(best, string) = SeqChars(i, string) /\ best <= i)

Init ==
  /\ string \in [ZeroIndexed -> CharacterSet]
  /\ length = Cardinality(string)
  /\ failure = [i \in ZeroIndexed |-> Sentinel]
  /\ patIndex = Sentinel
  /\ loop = 1
  /\ best = 0
  /\ pc = 1

OuterLoopCheck ==
  /\ loop < 2 * length
  /\ pc = 1
  /\ pc' = 2
  /\ UNCHANGED <<string, length, failure, patIndex, loop, best>>

FailureLookup ==
  /\ pc = 2
  /\ patIndex' = failure[(loop + best) % length]
  /\ pc' = 3
  /\ UNCHANGED <<string, length, failure, loop, best>>

InnerComparisonLoop ==
  /\ pc = 3
  /\ (SeqChars(loop % length, string) # SeqChars(patIndex % length, string) /\ patIndex # Sentinel)
  /\ pc' = 3
  /\ UNCHANGED <<string, length, failure, patIndex, loop, best>>

UpdateBestIfLess ==
  /\ pc = 3
  /\ (SeqChars(loop % length, string) # SeqChars(patIndex % length, string) /\ patIndex # Sentinel)
  /\ SeqChars(loop % length, string) < SeqChars(patIndex % length, string)
  /\ best' = loop % length
  /\ pc' = 4
  /\ UNCHANGED <<string, length, failure, patIndex, loop>>

FollowFailureChain ==
  /\ pc = 4
  /\ patIndex' = failure[patIndex]
  /\ pc' = 5
  /\ UNCHANGED <<string, length, failure, loop, best>>

PostComparison ==
  /\ pc = 5
  /\ (SeqChars(loop % length, string) # SeqChars(patIndex % length, string) /\ patIndex = Sentinel)
  /\ best' = (IF SeqChars(loop % length, string) < SeqChars(patIndex % length, string)
              THEN loop % length
              ELSE best)
  /\ failure' = [failure EXCEPT ![(loop + best) % length] =
                    IF patIndex # Sentinel
                    THEN patIndex + 1
                    ELSE Sentinel]
  /\ pc' = 6
  /\ UNCHANGED <<string, length, patIndex, loop>>

IncrementLoop ==
  /\ pc = 6
  /\ loop' = loop + 1
  /\ pc' = 1
  /\ UNCHANGED <<string, length, failure, patIndex, best>>

Terminate ==
  /\ loop >= 2 * length
  /\ pc = 1
  /\ pc' = 7
  /\ UNCHANGED <<string, length, failure, patIndex, loop, best>>

Stall ==
  /\ pc = 7
  /\ UNCHANGED vars

Next ==
  \/ OuterLoopCheck
  \/ FailureLookup
  \/ InnerComparisonLoop
  \/ UpdateBestIfLess
  \/ FollowFailureChain
  \/ PostComparison
  \/ IncrementLoop
  \/ Terminate
  \/ Stall

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Terminate)

====