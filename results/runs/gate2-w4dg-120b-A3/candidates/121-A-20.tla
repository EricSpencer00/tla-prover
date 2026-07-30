---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

VARIABLES inString, slen, fail, pm, loop, best, pc
vars == <<inString, slen, fail, pm, loop, best, pc>>

Calpha == 1
Sentinel == 0
MaxLen == 2

TypeInvariant ==
    /\ inString \in Seq(CharacterSet)
    /\ slen = Len(inString)
    /\ fail \in [0..(2 * slen) -> (0..(2 * slen)) \cup {Sentinel}]
    /\ pm \in 0..(2 * slen)
    /\ loop \in 1..(2 * slen)
    /\ best \in 0..(slen - 1)
    /\ pc \in {"outer", "lookup", "compare", "postcompare", "exit"}

Init ==
    /\ inString \in Seq(CharacterSet)
    /\ slen = Len(inString)
    /\ fail = [i \in 0..(2 * slen) |-> Sentinel]
    /\ pm = Sentinel
    /\ loop = 1
    /\ best = 0
    /\ pc = "outer"

OuterCheck ==
    /\ pc = "outer"
    /\ IF loop < (2 * slen) THEN pc' = "lookup" ELSE pc' = "exit"
    /\ UNCHANGED <<inString, slen, fail, pm, loop, best>>

Lookup ==
    /\ pc = "lookup"
    /\ pm' = fail[(loop - best) % slen]
    /\ pc' = "compare"
    /\ UNCHANGED <<inString, slen, fail, loop, best>>

Compare ==
    /\ pc = "compare"
    /\ pm # Sentinel
    /\ inString[(loop % slen) + 1] # inString[((loop - pm) % slen) + 1]
    /\ pc' = "compare"
    /\ UNCHANGED <<inString, slen, fail, pm, loop, best>>

UpdateBest ==
    /\ pc = "compare"
    /\ inString[(loop % slen) + 1] < inString[((loop - pm) % slen) + 1]
    /\ best' = loop % slen
    /\ UNCHANGED <<inString, slen, fail, pm, loop, pc>>

FollowChain ==
    /\ pc = "compare"
    /\ pm # Sentinel
    /\ pm' = fail[pm]
    /\ UNCHANGED <<inString, slen, fail, loop, best, pc>>

PostCompare ==
    /\ pc = "compare"
    /\ pm = Sentinel
    /\ pc' = "postcompare"
    /\ UNCHANGED <<inString, slen, fail, pm, loop, best>>

UpdateBest2 ==
    /\ pc = "postcompare"
    /\ inString[(loop % slen) + 1] < inString[((loop - best) % slen) + 1]
    /\ best' = loop % slen
    /\ UNCHANGED <<inString, slen, fail, pm, loop, pc>>

SetFail ==
    /\ pc = "postcompare"
    /\ pm = Sentinel
    /\ fail' = [fail EXCEPT ![(loop - best) % slen] = 1]
    /\ UNCHANGED <<inString, slen, pm, loop, best, pc>>

ResetFail ==
    /\ pc = "postcompare"
    /\ pm # Sentinel
    /\ fail' = [fail EXCEPT ![(loop - best) % slen] = Sentinel]
    /\ UNCHANGED <<inString, slen, pm, loop, best, pc>>

NextLoop ==
    /\ pc = "postcompare"
    /\ loop' = loop + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<inString, slen, fail, pm, best>>

Stall ==
    /\ pc = "exit"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ Compare
    \/ UpdateBest
    \/ FollowChain
    \/ PostCompare
    \/ UpdateBest2
    \/ SetFail
    \/ ResetFail
    \/ NextLoop
    \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(NextLoop)

Correctness ==
    /\ pc = "exit"
    /\ \A i \in 0..(slen - 1) : inString[best + 1..slen] ^ inString[1..best] <= inString[i + 1..slen] ^ inString[1..i]

Termination == <>(pc = "exit")

====