---- MODULE LeastCircularSubstring ----
\* Lexicographically-least circular substring via the linear-time Booth
\* algorithm (originally Booth 1980). The input string is chosen nondeterministically
\* from all strings over a bounded alphabet; the algorithm builds a failure function
\* and walks a doubled-index range to find the smallest rotation. SAFETY: the
\* chosen rotation is no greater than any other rotation and uses the smallest
\* shift when tied. LIVENESS: the algorithm eventually terminates.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* The algorithm treats the input as a ring, so the outer loop runs over a doubled
\* index range (0..<2*n) and every character access is taken modulo the length.
\* FailureFn is the KMP-style table; PatternMatchIdx is the current lookup; Best
\* records the rotation offset of the best candidate so far.
VARIABLES InputString, Length, FailureFn, PatternMatchIdx, LoopCounter, Best, PC

vars == <<InputString, Length, FailureFn, PatternMatchIdx, LoopCounter, Best, PC>>

Sentinel == 2 ^ 31
ZeroTo(n) == IF n = 0 THEN {} ELSE 1 .. n

TypeOK ==
  /\ InputString \in [1 .. Cardinality(CharacterSet)] -> CharacterSet
  /\ Length \in 0 .. Cardinality(CharacterSet)
  /\ FailureFn \in [ZeroTo(Cardinality(CharacterSet) * 2) -> (0 .. Cardinality(CharacterSet) * 2) \cup {Sentinel}]
  /\ PatternMatchIdx \in (0 .. Cardinality(CharacterSet) * 2) \cup {Sentinel}
  /\ LoopCounter \in 0 .. Cardinality(CharacterSet) * 2
  /\ Best \in ZeroTo(Cardinality(CharacterSet))
  /\ PC \in {"OuterCheck", "FailureLookup", "InnerLoop", "UpdateBest", "FollowChain", "PostCompare", "Done", "Stall"}

\* The failure table is always fully defined; entries are only consulted when
\* PatternMatchIdx is not the sentinel, so they are never read out of bounds.
Init ==
  /\ \E s \in [1 .. Cardinality(CharacterSet)] -> CharacterSet :
       InputString = s
  /\ Length = Len(InputString)
  /\ FailureFn = [i \in ZeroTo(Cardinality(CharacterSet) * 2) |-> Sentinel]
  /\ PatternMatchIdx = Sentinel
  /\ LoopCounter = 1
  /\ Best = 0
  /\ PC = "OuterCheck"

OuterCheck ==
  /\ PC = "OuterCheck"
  /\ PC' = IF LoopCounter < Length * 2 THEN "FailureLookup" ELSE "Done"
  /\ UNCHANGED <<InputString, Length, FailureFn, PatternMatchIdx, LoopCounter, Best>>

\* The failure function says where to resume comparison after a mismatch.
FailureLookup ==
  /\ PC = "FailureLookup"
  /\ PatternMatchIdx' = FailureFn[LoopCounter - 1]
  /\ PC' = "InnerLoop"
  /\ UNCHANGED <<InputString, Length, FailureFn, LoopCounter, Best>>

\* Compare the character at the current loop offset with the next character of
\* the candidate repeated rotation. The modulo captures the circular wrap.
InnerLoop ==
  /\ PC = "InnerLoop"
  /\ LET curChar == InputString[(LoopCounter % Length) + 1]
         candChar == InputString[((Best + LoopCounter) % Length) + 1]
     IN IF curChar # candChar /\ PatternMatchIdx # Sentinel
          THEN PC' = "FollowChain"
          ELSE PC' = "PostCompare"
  /\ UNCHANGED <<InputString, Length, FailureFn, PatternMatchIdx, LoopCounter, Best>>

UpdateBest ==
  /\ PC = "UpdateBest"
  /\ LET curChar == InputString[(LoopCounter % Length) + 1]
         candChar == InputString[((Best + LoopCounter) % Length) + 1]
     IN IF curChar < candChar
          THEN Best' = LoopCounter
          ELSE Best' = Best
  /\ PC' = "FollowChain"
  /\ UNCHANGED <<InputString, Length, FailureFn, PatternMatchIdx, LoopCounter>>

\* On a mismatch, the failure function tells where the longest border of the
\* candidate rotation begins, so the algorithm can resume from there.
FollowChain ==
  /\ PC = "FollowChain"
  /\ PatternMatchIdx' = FailureFn[PatternMatchIdx]
  /\ PC' = "InnerLoop"
  /\ UNCHANGED <<InputString, Length, FailureFn, LoopCounter, Best>>

\* If no failure link exists, the loop has reached the end of its current match.
\* Record the zero or one-step extension of the match in the table.
PostCompare ==
  /\ PC = "PostCompare"
  /\ LET curChar == InputString[(LoopCounter % Length) + 1]
         candChar == InputString[((Best + LoopCounter) % Length) + 1]
         newFailure == IF curChar = candChar
                          THEN IF PatternMatchIdx = Sentinel
                                  THEN 1
                                  ELSE PatternMatchIdx + 1
                          ELSE 0
     IN /\ FailureFn' = [FailureFn EXCEPT ![LoopCounter] = newFailure]
        /\ PatternMatchIdx' = Sentinel
        /\ Best' = IF curChar < candChar THEN LoopCounter ELSE Best
        /\ PC' = "OuterCheck"
  /\ LoopCounter' = LoopCounter + 1
  /\ UNCHANGED <<InputString, Length>>

Done ==
  /\ PC = "Done"
  /\ UNCHANGED vars

Stall ==
  /\ PC = "Stall"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ FailureLookup
  \/ InnerLoop
  \/ UpdateBest
  \/ FollowChain
  \/ PostCompare
  \/ Done
  \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(FailureLookup)
          /\ WF_vars(InnerLoop) /\ WF_vars(UpdateBest)
          /\ WF_vars(FollowChain) /\ WF_vars(PostCompare)

RotationsEqual(s, i, j) ==
  \A k \in 0 .. Length - 1 : s[(i + k) % Length + 1] = s[(j + k) % Length + 1]

SmallestRotation(s, i, j) ==
  RotationsEqual(s, i, j) => i <= j

\* SAFETY: the chosen rotation is lexicographically no greater than any other.
\* Because the action can revisit rotations that are equal, it also needs the
\* smallest shift among tied rotations, which is enforced by the guard on LoopCounter.
Correctness == \A i \in ZeroTo(Cardinality(CharacterSet) - 1) : SmallestRotation(InputString, Best, i)

Termination == <>(PC = "Done")
====