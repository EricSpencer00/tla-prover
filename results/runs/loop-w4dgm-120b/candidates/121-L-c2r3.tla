---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

\* The transformation below injects a FINITE character set into the public
\* signature of Sequences (which expects Nat) without touching Sequences.
CharacterSet == {1, 2}

Sequences == [ZSequences]Sequences EXCEPT !.CharacterSet = CharacterSet

CONSTANTS CharacterSet

VARIABLES inputString, strlen, fail, patIdx, outer, bestOffset, pc

vars == <<inputString, strlen, fail, patIdx, outer, bestOffset, pc>>

Corpus == UNION { [1..n -> CharacterSet] : n \in Nat }

MaxLen == 2  \* model checking bound, overridden by the .cfg

TypeOK ==
    /\ inputString \in Corpus
    /\ strlen = Len(inputString)
    /\ fail \in [0..2*strlen -> 0..strlen]
    /\ patIdx \in 0..strlen
    /\ outer \in 1..(2*strlen + 1)
    /\ bestOffset \in 0..(strlen - 1)
    /\ pc \in {"outerEntry","failLookup","innerComp","updateBest","followChain","postComp","increment","done"}

Init ==
    /\ inputString \in Corpus
    /\ strlen = Len(inputString)
    /\ fail = [i \in 0..(2*strlen) |-> 0]
    /\ patIdx = 0
    /\ outer = 1
    /\ bestOffset = 0
    /\ pc = "outerEntry"

OuterEntry ==
    /\ pc = "outerEntry"
    /\ outer <= 2 * strlen
    /\ pc' = "failLookup"
    /\ UNCHANGED <<inputString, strlen, fail, patIdx, outer, bestOffset>>

FailLookup ==
    /\ pc = "failLookup"
    /\ fail' = [fail EXCEPT ![outer - 1] = patIdx]
    /\ pc' = "innerComp"
    /\ UNCHANGED <<inputString, strlen, patIdx, outer, bestOffset>>

InnerComp ==
    /\ pc = "innerComp"
    /\ inputString[outer % strlen] # inputString[(bestOffset + outer) % strlen]
    /\ patIdx # 0
    /\ pc' = "postComp"
    /\ UNCHANGED <<inputString, strlen, fail, patIdx, outer, bestOffset>>

UpdateBest ==
    /\ pc = "innerComp"
    /\ inputString[outer % strlen] < inputString[(bestOffset + outer) % strlen]
    /\ bestOffset' = outer % strlen
    /\ pc' = "postComp"
    /\ UNCHANGED <<inputString, strlen, fail, patIdx, outer>>

FollowChain ==
    /\ pc = "postComp"
    /\ inputString[outer % strlen] # inputString[(bestOffset + outer) % strlen]
    /\ patIdx # 0
    /\ patIdx' = fail[patIdx]
    /\ pc' = "innerComp"
    /\ UNCHANGED <<inputString, strlen, fail, outer, bestOffset>>

PostComp ==
    /\ pc = "postComp"
    /\ (inputString[outer % strlen] = inputString[(bestOffset + outer) % strlen] \/ patIdx = 0)
    /\ IF patIdx = 0
       THEN IF inputString[outer % strlen] < inputString[(bestOffset + outer) % strlen]
             THEN bestOffset' = outer % strlen
             ELSE bestOffset' = bestOffset
            /\ fail' = [fail EXCEPT ![outer - 1] = 0]
       ELSE fail' = [fail EXCEPT ![outer - 1] = patIdx + 1]
    /\ pc' = "increment"
    /\ UNCHANGED <<inputString, strlen, patIdx, outer>>

Increment ==
    /\ pc = "increment"
    /\ outer' = outer + 1
    /\ pc' = "outerEntry"
    /\ UNCHANGED <<inputString, strlen, fail, patIdx, bestOffset>>

Done ==
    /\ pc = "outerEntry"
    /\ outer > 2 * strlen
    /\ pc' = "done"
    /\ UNCHANGED <<inputString, strlen, fail, patIdx, outer, bestOffset>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterEntry
    \/ FailLookup
    \/ InnerComp
    \/ UpdateBest
    \/ FollowChain
    \/ PostComp
    \/ Increment
    \/ Done
    \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Done)

TypeInvariant == TypeOK

\* The lexicographically-minimal rotation dominates every other offset,
\* and among equal rotations (periodic strings) it has the smallest shift.
Correctness ==
    /\ \A i \in 0..(strlen - 1) : inputString[(bestOffset + i) % strlen] <= inputString[i]
    /\ \A i \in 0..(strlen - 1) :
        (inputString[(bestOffset + i) % strlen] = inputString[i])
          => bestOffset <= i

Termination == (\E i \in 0..(strlen - 1) : bestOffset = i) ~> (pc = "done")

====