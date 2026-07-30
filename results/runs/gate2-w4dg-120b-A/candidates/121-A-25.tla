---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet, Nat

\* inputString is the nondeterministic corpus (all zero-indexed strings).
\* failure is the KMP-like failure function, failure[i] is undefined (\*).
\* bestOffset tracks the lexicographically-minimal rotation start position.
\* pc is the labeled step counter; loopCounter drives the outer loop.
VARIABLES inputString, strLen, failure, matchIdx, loopCounter, bestOffset, pc

vars == <<inputString, strLen, failure, matchIdx, loopCounter, bestOffset, pc>>

Uninitialized == "uninitialized"

TypeInvariant ==
  /\ inputString \in UNION {[1..n -> CharacterSet] : n \in 1..Nat}
  /\ strLen \in 1..Nat
  /\ Len(inputString) = strLen
  /\ failure \in [0..(2 * Nat) -> (0..Nat) \cup {Uninitialized}]
  /\ matchIdx \in (0..Nat) \cup {Uninitialized}
  /\ loopCounter \in 1..(2 * Nat)
  /\ bestOffset \in 0..(strLen - 1)
  /\ pc \in {"outerCheck", "lookup", "compareLoop", "extendMatch",
             "followFailure", "postCompare", "increment", "done"}

Init ==
  /\ \E s \in UNION {[1..n -> CharacterSet] : n \in 1..Nat} :
       inputString' = s
  /\ strLen' = Len(inputString)
  /\ failure' = [i \in 0..(2 * Nat) |-> Uninitialized]
  /\ matchIdx' = Uninitialized
  /\ loopCounter' = 1
  /\ bestOffset' = 0
  /\ pc' = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loopCounter < (2 * strLen) THEN pc' = "lookup" ELSE pc' = "done"
  /\ UNCHANGED <<inputString, strLen, failure, matchIdx,
                 loopCounter, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ IF matchIdx = Uninitialized THEN pc' = "compareLoop"
     ELSE pc' = "compareLoop"
  /\ UNCHANGED <<inputString, strLen, failure, matchIdx,
                 loopCounter, bestOffset>>

CompareLoop ==
  /\ pc = "compareLoop"
  /\ LET curChar == inputString[(loopCounter % strLen) + 1]
         candChar == inputString[(bestOffset + matchIdx) % strLen + 1]
         matchChar == inputString[(bestOffset + loopCounter) % strLen + 1]
     IN IF curChar = matchChar THEN pc' = "extendMatch"
        ELSE IF matchIdx = Uninitialized THEN pc' = "postCompare"
        ELSE pc' = "followFailure"
  /\ UNCHANGED <<inputString, strLen, failure, matchIdx,
                 loopCounter, bestOffset>>

ExtendMatch ==
  /\ pc = "extendMatch"
  /\ LET curChar == inputString[(loopCounter % strLen) + 1]
         candChar == inputString[(bestOffset + loopCounter) % strLen + 1]
     IN IF curChar < candChar /\ matchIdx # Uninitialized
           THEN bestOffset' = loopCounter
           ELSE bestOffset' = bestOffset
  /\ pc' = "followFailure"
  /\ UNCHANGED <<inputString, strLen, failure, matchIdx,
                 loopCounter>>

FollowFailure ==
  /\ pc = "followFailure"
  /\ matchIdx' = failure[loopCounter]
  /\ pc' = "compareLoop"
  /\ UNCHANGED <<inputString, strLen, failure, loopCounter, bestOffset>>

PostCompare ==
  /\ pc = "postCompare"
  /\ LET curChar == inputString[(loopCounter % strLen) + 1]
         candChar == inputString[(bestOffset + loopCounter) % strLen + 1]
     IN bestOffset' = IF curChar < candChar THEN loopCounter ELSE bestOffset
  /\ failure' = [failure EXCEPT ![loopCounter] =
                   IF matchIdx = Uninitialized THEN Uninitialized
                   ELSE matchIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, matchIdx, loopCounter>>

Increment ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, strLen, failure, matchIdx, bestOffset>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ Lookup \/ CompareLoop \/ ExtendMatch
  \/ FollowFailure \/ PostCompare \/ Increment \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* At termination the identified rotation is lexicographically minimal.
Correctness ==
  /\ pc = "done"
  /\ \A k \in 0..(strLen - 1) :
       LET rot(k) == inputString[((bestOffset + k) % strLen) + 1]
           lex(seq) == \E i \in 1..Len(seq) : seq[i] = Min(seq)
       IN rot(k) >= rot(0) /\ (rot(k) = rot(0) => k >= 0)

Termination == <>(pc = "done")

====