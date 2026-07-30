---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* ZSequences is a zero-indexed version of Naturals.  CharacterSet replaces the
\* standard Nat in the model configuration, so here we inherit the full Nat and
\* simply treat it as a finite subset.
\* (The .cfg file swaps ZSequences.Nat for Nat; keep EXTENDS Naturals here.)
ASSUME CharacterSet \subseteq Nat

Sequences == [0 .. 2]
Sentinel == 99

VARIABLES inputString, strLen, failure, patIdx, counter, bestOffset, pc
vars == <<inputString, strLen, failure, patIdx, counter, bestOffset, pc>>

Init ==
  /\ \E s \in Seq(CharacterSet) : inputString = s
  /\ strLen = Len(inputString)
  /\ failure = [i \in 0 .. 2 * strLen |-> Sentinel]
  /\ patIdx = Sentinel
  /\ counter = 1
  /\ bestOffset = 0
  /\ pc = "outer"

OuterCheck ==
  /\ pc = "outer"
  /\ IF counter < 2 * strLen
       THEN pc' = "lookup"
       ELSE pc' = "done"
  /\ UNCHANGED <<inputString, strLen, failure, patIdx, counter, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ patIdx' = failure[(counter - bestOffset) % strLen]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, strLen, failure, counter, bestOffset>>

Compare ==
  /\ pc = "compare"
  /\ LET cur == inputString[counter % strLen]
         cand == inputString[(bestOffset + counter) % strLen]
     IN IF cur # cand /\ patIdx # Sentinel
           THEN pc' = "compare"
           ELSE pc' = "post"
  /\ UNCHANGED <<inputString, strLen, failure, patIdx, counter, bestOffset>>

UpdateOnLess ==
  /\ pc = "compare"
  /\ LET cur == inputString[counter % strLen]
         cand == inputString[(bestOffset + counter) % strLen]
     IN cur < cand
  /\ bestOffset' = counter
  /\ UNCHANGED <<inputString, strLen, failure, patIdx, counter, pc>>

FollowChain ==
  /\ pc = "compare"
  /\ patIdx # Sentinel
  /\ patIdx' = failure[patIdx]
  /\ UNCHANGED <<inputString, strLen, failure, counter, bestOffset, pc>>

PostComparison ==
  /\ pc = "post"
  /\ LET cur == inputString[counter % strLen]
         cand == inputString[(bestOffset + counter) % strLen]
     IN IF cur # cand /\ patIdx = Sentinel /\ cur < cand
          THEN bestOffset' = counter
          ELSE bestOffset' = bestOffset
  /\ failure' = [failure EXCEPT ![counter % strLen] = IF patIdx = Sentinel
                                            THEN Sentinel
                                            ELSE patIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, patIdx, counter>>

Increment ==
  /\ pc = "increment"
  /\ counter' = counter + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputString, strLen, failure, patIdx, bestOffset>>

DoneStall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ Lookup \/ Compare \/ UpdateOnLess
  \/ FollowChain \/ PostComparison \/ Increment \/ DoneStall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Lookup)
        /\ WF_vars(Compare) /\ WF_vars(PostComparison) /\ WF_vars(Increment)

TypeInvariant ==
  /\ inputString \in Seq(CharacterSet)
  /\ strLen = Len(inputString)
  /\ failure \in [0 .. 2 * strLen -> 0 .. 2 * strLen \cup {Sentinel}]
  /\ patIdx \in 0 .. 2 * strLen \cup {Sentinel}
  /\ counter \in 1 .. 2 * strLen
  /\ bestOffset \in 0 .. strLen - 1

Rotate(s, k) == <<s[(k + i) % Len(s)] : i \in DOMAIN s>>
RotationAt(s, k) == Rotation(s, k)
AllRotations(s) == {RotationAt(s, k) : k \in 0 .. Len(s) - 1}

Correctness ==
  LET res == RotationAt(inputString, bestOffset) IN
    /\ res \in AllRotations(inputString)
    /\ \A k \in 0 .. strLen - 1 : res <= RotationAt(inputString, k)
    /\ (\A k \in 0 .. strLen - 1 : res = RotationAt(inputString, k) => k >= bestOffset)

Termination == <>(pc = "done")

====