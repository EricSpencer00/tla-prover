---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CharacterSet

ASSUME CharacterSet \subseteq Nat /\ CharacterSet # {}

VARIABLES inputString, length, failure, pattern, loopCounter, bestOffset, pc
vars == <<inputString, length, failure, pattern, loopCounter, bestOffset, pc>>

StringSpace == UNION { [1 .. n -> CharacterSet] : n \in (Nat \ {0}) }
FAILURE_SENTINEL == 0
MaxLength == 3

Init ==
  /\ inputString \in StringSpace
  /\ length = Len(inputString)
  /\ failure = [i \in 0 .. 2 * length |-> FAILURE_SENTINEL]
  /\ pattern = FAILURE_SENTINEL
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ IF loopCounter < 2 * length
       THEN /\ pc' = "lookup"
            /\ UNCHANGED <<inputString, length, failure, pattern, loopCounter, bestOffset>>
       ELSE /\ pc' = "done"
            /\ UNCHANGED <<inputString, length, failure, pattern, loopCounter, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ pattern' = failure[(loopCounter + bestOffset) % length]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset>>

Compare ==
  /\ pc = "compare"
  /\ LET curChar == inputString[(loopCounter % length) + 1]
         candChar == inputString[((pattern + bestOffset) % length) + 1]
     IN /\ ((curChar = candChar) /\ pattern # FAILURE_SENTINEL) \/ pc' = "post"
        /\ (pattern' = IF pattern # FAILURE_SENTINEL THEN pattern ELSE pattern)
  /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset>>

UpdateBest ==
  /\ pc = "compare"
  /\ LET curChar == inputString[(loopCounter % length) + 1]
         candChar == inputString[((pattern + bestOffset) % length) + 1]
         curChar1 == inputString[(loopCounter % length) + 1]
         candChar1 == inputString[((pattern + 1 + bestOffset) % length) + 1]
     IN /\ curChar < candChar
        /\ bestOffset' = loopCounter % length
        /\ failure' = [failure EXCEPT ![(pattern + bestOffset + 1) % length] = pattern + 1]
  /\ pc' = "follow"
  /\ UNCHANGED <<inputString, length, pattern, loopCounter>>

Follow ==
  /\ pc = "compare"
  /\ pattern # FAILURE_SENTINEL
  /\ pattern' = failure[(pattern + bestOffset) % length]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset>>

Post ==
  /\ pc = "post"
  /\ LET curChar == inputString[(loopCounter % length) + 1]
         candChar == inputString[((pattern + bestOffset) % length) + 1]
         curChar1 == inputString[(loopCounter % length) + 1]
         candChar1 == inputString[((pattern + 1 + bestOffset) % length) + 1]
     IN /\ ((curChar # candChar) /\ pattern = FAILURE_SENTINEL /\ curChar < candChar)
        /\ bestOffset' = loopCounter % length
        /\ failure' = [failure EXCEPT ![(pattern + bestOffset + 1) % length] = pattern + 1]
  /\ pattern' = FAILURE_SENTINEL
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, length, loopCounter>>

Increment ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputString, length, failure, pattern, bestOffset>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == OuterLoop \/ Lookup \/ Compare \/ UpdateBest \/ Follow \/ Post \/ Increment \/ Done

TypeInvariant ==
  /\ inputString \in StringSpace
  /\ length = Len(inputString)
  /\ failure \in [0 .. 2 * length -> 0 .. 2 * length]
  /\ pattern \in 0 .. 2 * length
  /\ loopCounter \in 1 .. 2 * length + 1
  /\ bestOffset \in 0 .. (IF length = 0 THEN 0 ELSE length - 1)
  /\ pc \in {"outer", "lookup", "compare", "post", "increment", "done"}

Spec == Init /\ [][Next]_vars /\ WF_vars(Lookup) /\ WF_vars(Compare) /\ WF_vars(Post) /\ WF_vars(Increment)

Rotations(s) == { s[i .. Len(s)] ^ s[1 .. i - 1] : i \in DOMAIN s }
LexLess(s, t) == (\E i \in DOMAIN s : (\A j \in 1 .. (i - 1) : s[j] = t[j]) /\ s[i] < t[i])
MinRotations(s) == { r \in Rotations(s) : (\A t \in Rotations(s) : LexLess(r, t) \/ r = t) }

Correctness ==
  /\ bestOffset \in 0 .. (IF length = 0 THEN 0 ELSE length - 1)
  /\ LET bestRot == inputString[bestOffset + 1 .. length] ^ inputString[1 .. bestOffset]
         mins == MinRotations(inputString)
     IN /\ bestRot \in mins
        /\ (\A r \in mins : bestOffset <= (CHOOSE i \in DOMAIN inputString : r = inputString[i .. Len(inputString)] ^ inputString[1 .. i - 1]))

Termination == <>(pc = "done")
====