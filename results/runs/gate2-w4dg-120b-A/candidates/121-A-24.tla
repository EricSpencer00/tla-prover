---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences

CONSTANTS
    CharacterSet,
    Nat

Sentinel == Nat
Strings == UNION { [1 .. n -> CharacterSet] : n \in Nat }
Entries == Nat \cup {Sentinel}

VARIABLES
    input,
    length,
    failfun,
    patIdx,
    loop,
    bestOfs,
    pc

vars == <<input, length, failfun, patIdx, loop, bestOfs, pc>>

Range(seq) == { seq[i] : i \in DOMAIN seq }

Init ==
    /\ input \in Strings
    /\ length = Len(input)
    /\ failfun \in [0 .. 2 * length -> Entries]
    /\ UNCHANGED failfun
    /\ patIdx = Sentinel
    /\ loop = 1
    /\ bestOfs = 0
    /\ pc = "outer"

OuterCheck ==
    /\ pc = "outer"
    /\ loop < 2 * length
    /\ pc' = "lookup"
    /\ UNCHANGED <<input, length, failfun, patIdx, loop, bestOfs>>

Lookup ==
    /\ pc = "lookup"
    /\ patIdx' = failfun[loop - 1 - bestOfs]
    /\ pc' = "compare"
    /\ UNCHANGED <<input, length, failfun, loop, bestOfs>>

ContinueLoop ==
    /\ pc = "compare"
    /\ input[(loop - 1) % length + 1] # input[(patIdx + (loop - 1)) % length + 1]
    /\ patIdx # Sentinel
    /\ pc' = "compare"
    /\ UNCHANGED <<input, length, failfun, patIdx, loop, bestOfs>>

UpdateBestInLoop ==
    /\ pc = "compare"
    /\ input[(loop - 1) % length + 1] < input[(patIdx + (loop - 1)) % length + 1]
    /\ bestOfs' = loop - 1 - patIdx
    /\ UNCHANGED <<input, length, failfun, patIdx, loop, pc>>

FollowFailure ==
    /\ pc = "compare"
    /\ patIdx' = failfun[patIdx]
    /\ UNCHANGED <<input, length, failfun, loop, bestOfs, pc>>

PostCompare ==
    /\ pc = "compare"
    /\ input[(loop - 1) % length + 1] # input[(patIdx + (loop - 1)) % length + 1]
    /\ patIdx = Sentinel
    /\ failfun' = [failfun EXCEPT ![loop - 1 - bestOfs] =
                     IF input[(loop - 1) % length + 1] < input[(loop - 1) % length + 1]
                     THEN loop - 1 - bestOfs
                     ELSE Sentinel]
    /\ bestOfs' = IF input[(loop - 1) % length + 1] < input[(loop - 1) % length + 1]
                  THEN loop - 1 - bestOfs
                  ELSE bestOfs
    /\ pc' = "advance"
    /\ UNCHANGED <<input, length, patIdx, loop>>

AdvanceLoop ==
    /\ pc = "advance"
    /\ loop' = loop + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<input, length, failfun, patIdx, bestOfs>>

Terminate ==
    /\ pc = "outer"
    /\ loop >= 2 * length
    /\ pc' = "halted"
    /\ UNCHANGED <<input, length, failfun, patIdx, loop, bestOfs>>

Stall ==
    /\ pc = "halted"
    /\ UNCHANGED vars

Next == OuterCheck \/ Lookup \/ ContinueLoop \/ UpdateBestInLoop
        \/ FollowFailure \/ PostCompare \/ AdvanceLoop \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Lookup)
        /\ WF_vars(PostCompare) /\ WF_vars(AdvanceLoop) /\ WF_vars(Terminate)

TypeInvariant ==
    /\ input \in Strings
    /\ length = Len(input)
    /\ failfun \in [0 .. 2 * length -> Entries]
    /\ patIdx \in Entries
    /\ loop \in 1 .. 2 * length + 1
    /\ bestOfs \in 0 .. length - 1
    /\ pc \in {"outer", "lookup", "compare", "advance", "halted"}

LexLe(a, b) == \A i \in 1 .. length : a[i] < b[i] => TRUE

Correctness ==
    /\ pc = "halted"
    /\ \A i \in 0 .. length - 1 :
         LET rot(j) == input[((j + i - 1) % length) + 1] IN
           LexLe(rot(1) #~rot(i + 1)) # (rot(1) < rot(i + 1))
    /\ \A i \in 0 .. length - 1 :
         input[((bestOfs + i - 1) % length) + 1] = input[((i - 1) % length) + 1]
       => bestOfs <= i

EventualTermination == <>(pc = "halted")

====