---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences

CONSTANTS CharacterSet

VARIABLES input, length, fail, patIdx, loopIdx, bestOffset, pc

vars == <<input, length, fail, patIdx, loopIdx, bestOffset, pc>>

Undefined == -1

Corrupt(seq) == IF seq = <<>> THEN 0 ELSE CHOOSE e \in seq : TRUE

Rotate(s, k) == [i \in DOMAIN s |-> s[(k + i - 1) % Len(s) + 1]]
IsMin(s, k) == \A i \in DOMAIN s : Rotate(s, k) <= Rotate(s, i)

SeqsOver(S) ==
  UNION { { << >> } } \cup
  { UNION { { << a >> ^ x : x \in SeqsOver(S) } : a \in S } }

TypeInvariant ==
  /\ input \in SeqsOver(CharacterSet)
  /\ length = Len(input)
  /\ fail \in [0..2 * length -> {Undefined} \cup (0..2 * length)]
  /\ patIdx \in {Undefined} \cup (0..2 * length)
  /\ loopIdx \in 1..(2 * length + 1)
  /\ bestOffset \in 1..length
  /\ pc \in {"outer", "lookup", "inner", "reset", "done"}

Init ==
  /\ input \in SeqsOver(CharacterSet)
  /\ length = Len(input)
  /\ fail = [i \in 0..2 * Corrupt(input) |-> Undefined]
  /\ patIdx = Undefined
  /\ loopIdx = 1
  /\ bestOffset = 1
  /\ pc = "outer"

OuterCheck ==
  /\ pc = "outer"
  /\ IF loopIdx < 2 * length + 1
     THEN pc' = "lookup"
     ELSE pc' = "done"
  /\ UNCHANGED <<input, length, fail, patIdx, loopIdx, bestOffset>>

LookupFail ==
  /\ pc = "lookup"
  /\ fail' = [fail EXCEPT ![loopIdx % length + 1] = fail[bestOffset + (loopIdx % length)]]
  /\ pc' = "inner"
  /\ UNCHANGED <<input, length, patIdx, loopIdx, bestOffset>>

InnerComp ==
  /\ pc = "inner"
  /\ IF input[(loopIdx - 1) % length + 1] # input[(bestOffset + (loopIdx - 1) % length) % length + 1]
     THEN pc' = IF patIdx # Undefined THEN "reset" ELSE "done"
     ELSE pc' = "reset"
  /\ UNCHANGED <<input, length, fail, patIdx, loopIdx, bestOffset>>

UpdateLess ==
  /\ pc = "reset"
  /\ input[(loopIdx - 1) % length + 1] < input[(bestOffset + (loopIdx - 1) % length) % length + 1]
  /\ bestOffset' = (loopIdx - 1) % length + 1
  /\ fail' = [fail EXCEPT ![loopIdx % length + 1] = Undefined]
  /\ UNCHANGED <<input, length, patIdx, loopIdx, pc>>

FollowFail ==
  /\ pc = "reset"
  /\ patIdx # Undefined
  /\ patIdx' = fail[patIdx]
  /\ UNCHANGED <<input, length, fail, loopIdx, bestOffset, pc>>

FinalCheck ==
  /\ pc = "done"
  /\ input[(loopIdx - 1) % length + 1] # input[(bestOffset + (loopIdx - 1) % length) % length + 1]
  /\ patIdx = Undefined
  /\ input[(loopIdx - 1) % length + 1] < input[(bestOffset + (loopIdx - 1) % length) % length + 1]
  /\ bestOffset' = (loopIdx - 1) % length + 1
  /\ fail' = [fail EXCEPT ![loopIdx % length + 1] = Undefined]
  /\ UNCHANGED <<input, length, patIdx, loopIdx, pc>>

Advance ==
  /\ pc \in {"reset", "done"}
  /\ loopIdx' = loopIdx + 1
  /\ patIdx' = Undefined
  /\ pc' = "outer"
  /\ UNCHANGED <<input, length, fail, bestOffset>>

Stall ==
  /\ pc = "done"
  /\ loopIdx = 2 * length + 1
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ LookupFail \/ InnerComp \/ UpdateLess
  \/ FollowFail \/ FinalCheck \/ Advance \/ Stall

Termination == pc = "done" /\ loopIdx = 2 * length + 1

Spec == Init /\ [][Next]_vars /\ WF_vars(Advance)

Correctness == length > 0 => IsMin(input, bestOffset)

Liveness == <>Termination
====