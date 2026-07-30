---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

\* Sequence indexing is zero-based here, not standard one-based, and the
\* circular wrap-around is modelled by indexing modulo the string length.
\* The .cfg file replaces the built-in Nat with a finite version of it,
\* so the model stays bounded.
[ZSequences]CharacterSet

CONSTANT MaxLength
VARIABLES inputString, n, fail, pIdx, i, bestOffset, pc

vars == <<inputString, n, fail, pIdx, i, bestOffset, pc>>

NumStrings == Cardinality(CharacterSet) ^ n

Sentinel == MaxLength
MaxIdx == 2 * MaxLength
MaxLoop == 2 * MaxLength

TypeOK ==
  /\ inputString \in [0..(n - 1) -> CharacterSet]
  /\ n \in 0..MaxLength
  /\ fail \in [0..MaxIdx -> 0..MaxIdx \cup {Sentinel}]
  /\ pIdx \in 0..MaxIdx \cup {Sentinel}
  /\ i \in 0..MaxLoop
  /\ bestOffset \in 0..(n - 1)
  /\ pc \in {"outer", "lookup", "inner", "postInner", "rewind", "done"}

Init ==
  /\ inputString \in [0..MaxLength -> CharacterSet]
  /\ n \in 1..MaxLength
  /\ fail = [k \in 0..MaxIdx |-> Sentinel]
  /\ pIdx = Sentinel
  /\ i = 1
  /\ bestOffset = 0
  /\ pc = "outer"

OuterCheck ==
  /\ pc = "outer"
  /\ i < 2 * n
  /\ pc' = "lookup"
  /\ UNCHANGED <<inputString, n, fail, pIdx, i, bestOffset>>

LookupFailure ==
  /\ pc = "lookup"
  /\ fail' = [fail EXCEPT ![i + bestOffset] = Sentinel]
  /\ pIdx' = fail[i + bestOffset]
  /\ pc' = "inner"
  /\ UNCHANGED <<inputString, n, i, bestOffset>>

\* Compare the character at the current position with the one at the
\* candidate rotation, wrapping around the string.
InnerLoop ==
  /\ pc = "inner"
  /\ i \in 0..(2 * n - 1)
  /\ inputString[i % n] # inputString[(bestOffset + i) % n]
  /\ pIdx # Sentinel
  /\ pc' = "postInner"
  /\ UNCHANGED <<inputString, n, fail, pIdx, i, bestOffset>>

UpdateBestOnLess ==
  /\ pc = "inner"
  /\ inputString[i % n] < inputString[(bestOffset + i) % n]
  /\ bestOffset' = i
  /\ UNCHANGED <<inputString, n, fail, pIdx, i, pc>>

FollowFailure ==
  /\ pc = "postInner"
  /\ pIdx # Sentinel
  /\ pIdx' = fail[pIdx]
  /\ pc' = "rewind"
  /\ UNCHANGED <<inputString, n, fail, i, bestOffset>>

FinalCompare ==
  /\ pc = "postInner"
  /\ inputString[i % n] # inputString[(bestOffset + i) % n]
  /\ pIdx = Sentinel
  /\ inputString[i % n] < inputString[(bestOffset + i) % n]
  /\ bestOffset' = i
  /\ UNCHANGED <<inputString, n, pIdx, i, pc>>

ResetFailure ==
  /\ pc = "postInner"
  /\ inputString[i % n] # inputString[(bestOffset + i) % n]
  /\ pIdx = Sentinel
  /\ inputString[i % n] >= inputString[(bestOffset + i) % n]
  /\ fail' = [fail EXCEPT ![i + bestOffset] = Sentinel]
  /\ UNCHANGED <<inputString, n, pIdx, i, bestOffset, pc>>

ExtendFailure ==
  /\ pc = "postInner"
  /\ inputString[i % n] = inputString[(bestOffset + i) % n]
  /\ fail' = [fail EXCEPT ![i + bestOffset] = IF pIdx = Sentinel THEN 1 ELSE pIdx + 1]
  /\ UNCHANGED <<inputString, n, pIdx, i, bestOffset, pc>>

Rewind ==
  /\ pc = "rewind"
  /\ pc' = "outer"
  /\ i' = i + 1
  /\ UNCHANGED <<inputString, n, fail, pIdx, bestOffset>>

Terminate ==
  /\ pc = "outer"
  /\ i >= 2 * n
  /\ pc' = "done"
  /\ UNCHANGED <<inputString, n, fail, pIdx, i, bestOffset>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ LookupFailure
  \/ InnerLoop
  \/ UpdateBestOnLess
  \/ FollowFailure
  \/ FinalCompare
  \/ ResetFailure
  \/ ExtendFailure
  \/ Rewind
  \/ Terminate
  \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Terminate)

\* Correctness: the minimal rotation found by the algorithm is not only
\* lexicographically minimal, but also the one with the smallest shift
\* among rotations producing the same sequence.
MinimalLexicographically ==
  /\ \A j \in 1..(n - 1) : inputString[(bestOffset + j) % n] >= inputString[(j) % n]
  /\ \A k \in 0..(n - 1) :
       \/ inputString[(k + bestOffset) % n] > inputString[k]
       \/ (inputString[(k + bestOffset) % n] = inputString[k] /\ bestOffset <= k)

\* The algorithm always reaches its terminal state (progress property).
Termination == <>(pc = "done")

StandardTemporal ==
  /\ TypeOK
  /\ MinimalLexicographically
  /\ Termination

====