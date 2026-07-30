---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet, Nat

\* The empty sequence of characters (for the zero-length edge case).
EmptySeq == << >>

\* The corpus of all zero-indexed sequences over the character set up to the
\* maximum length configured by the model checker.
Corpus == { s \in Seq(CharacterSet) : Len(s) <= Nat }

Sentinel == Nat + 1

VARIABLES inputString, length, failure, matchIdx, loop, bestOffset, pc

vars == << inputString, length, failure, matchIdx, loop, bestOffset, pc >>

TypeInvariant ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure \in [0..(2 * Nat) -> 0..(Nat + 1)]
  /\ matchIdx \in 0..(Nat + 1)
  /\ loop \in 1..(2 * Nat)
  /\ bestOffset \in 0..Nat
  /\ pc \in {"outer", "lookup", "compare", "fail", "follow", "post", "done"}

Init ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure = [i \in 0..(2 * Nat) |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ loop = 1
  /\ bestOffset = 0
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ IF loop < (2 * Nat)
       THEN pc' = "lookup"
       ELSE pc' = "done"
  /\ UNCHANGED << inputString, length, failure, matchIdx, loop, bestOffset >>

Lookup ==
  /\ pc = "lookup"
  /\ matchIdx' = failure[loop - bestOffset]
  /\ pc' = "compare"
  /\ UNCHANGED << inputString, length, failure, loop, bestOffset >>

\* Compare the character at the current loop position with the character
\* at the candidate position in the rotated view.
Compare ==
  /\ pc = "compare"
  /\ IF (inputString[loop % length] # inputString[bestOffset % length])
       /\ matchIdx # Sentinel
       THEN pc' = "compare"
       ELSE pc' = "post"
  /\ UNCHANGED << inputString, length, failure, matchIdx, loop, bestOffset >>

\* A strictly smaller character at the current position beats the previous best.
UpdateBest ==
  /\ inputString[loop % length] < inputString[bestOffset % length]
  /\ bestOffset' = loop % length
  /\ UNCHANGED << inputString, length, failure, matchIdx, loop, pc >>

Follow ==
  /\ pc = "post"
  /\ matchIdx # Sentinel
  /\ matchIdx' = failure[matchIdx]
  /\ pc' = "outer"
  /\ loop' = loop + 1
  /\ UNCHANGED << inputString, length, failure, bestOffset >>

Fail ==
  /\ pc = "post"
  /\ matchIdx = Sentinel
  /\ inputString[loop % length] # inputString[bestOffset % length]
  /\ bestOffset' = IF inputString[loop % length] < inputString[bestOffset % length]
                      THEN loop % length
                      ELSE bestOffset
  /\ failure' = [failure EXCEPT ![loop - bestOffset] = matchIdx + 1]
  /\ pc' = "outer"
  /\ loop' = loop + 1
  /\ UNCHANGED << inputString, length, matchIdx >>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop
  \/ Lookup
  \/ Compare
  \/ UpdateBest
  \/ Follow
  \/ Fail
  \/ Done

Spec == Init /\ [][Next]_vars

\* At termination the best offset yields a rotation that is lexicographically
\* no greater than any other rotation, with ties broken by the smallest shift.
Correctness ==
  /\ pc = "done"
  /\ \A i \in 1..length :
       LET r1 == << inputString[(bestOffset + k) % length] : k \in 0..(length - 1) >>
           r2 == << inputString[(i + k) % length] : k \in 0..(length - 1) >>
       IN r1 <= r2
  /\ \A i \in 1..length :
       LET r1 == << inputString[(bestOffset + k) % length] : k \in 0..(length - 1) >>
           r2 == << inputString[(i + k) % length] : k \in 0..(length - 1) >>
       IN r1 = r2 => bestOffset <= i

Termination ==
  (\A i \in 1..Nat : [][pc = "outer"]_vars) ~> (pc = "done")

====