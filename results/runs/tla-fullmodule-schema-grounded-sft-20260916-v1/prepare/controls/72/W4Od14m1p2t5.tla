---------------------------- MODULE W4Od14m1p2t5 ----------------------------
EXTENDS Naturals

CONSTANTS TotalTokens, MaxData, MaxCount

VARIABLES holds, dataCount, passes, overrides, lastActive

vars == <<holds, dataCount, passes, overrides, lastActive>>

Drones == 0 .. 2

NextD(d) == (d + 1) % 3

PrevD(d) == (d + 2) % 3

Total == holds[0] + holds[1] + holds[2]

Bump(n) == IF n < MaxCount THEN n + 1 ELSE n

Init ==
    /\ holds = [d \in Drones |-> IF d = 0 THEN TotalTokens ELSE 0]
    /\ dataCount = 0
    /\ passes = 0
    /\ overrides = 0
    /\ lastActive = 0

Pass(d) ==
    /\ holds[d] > 0
    /\ holds' = [holds EXCEPT ![d] = @ - 1, ![NextD(d)] = @ + 1]
    /\ passes' = Bump(passes)
    /\ lastActive' = NextD(d)
    /\ UNCHANGED <<dataCount, overrides>>

Access(d) ==
    /\ holds[d] > 0
    /\ dataCount < MaxData
    /\ dataCount' = dataCount + 1
    /\ lastActive' = d
    /\ UNCHANGED <<holds, passes, overrides>>

AdminOverride ==
    /\ overrides < MaxCount
    /\ holds' = [d \in Drones |-> IF d = 0 THEN TotalTokens ELSE 0]
    /\ overrides' = overrides + 1
    /\ lastActive' = 0
    /\ UNCHANGED <<dataCount, passes>>

PassBack(d) ==
    /\ holds[d] > 0
    /\ holds' = [holds EXCEPT ![d] = @ - 1, ![PrevD(d)] = @ + 1]
    /\ passes' = Bump(passes)
    /\ lastActive' = PrevD(d)
    /\ UNCHANGED <<dataCount, overrides>>

Next ==
    \/ \E d \in Drones : Pass(d)
    \/ \E d \in Drones : PassBack(d)
    \/ \E d \in Drones : Access(d)
    \/ AdminOverride

Spec == Init /\ [][Next]_vars

TokenConservation ==
    Total = TotalTokens
===========================================================================