---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES stage, myRead, slow

vars == <<stage, myRead, slow>>

Stages == {"idle", "reading", "inCS"}
NoRead == MaxNat + 1

TypeOK ==
  /\ stage \in [1..N -> Stages]
  /\ myRead \in [1..N -> 0..(MaxNat + 1)]
  /\ slow \in [1..N -> BOOLEAN]

Init ==
  /\ stage = [p \in 1..N |-> "idle"]
  /\ myRead = [p \in 1..N |-> NoRead]
  /\ slow = [p \in 1..N |-> FALSE]

MutualExclusion ==
  \A p, q \in 1..N : (stage[p] = "inCS" /\ stage[q] = "inCS") => p = q

Inv ==
  /\ \A p \in 1..N : (stage[p] = "reading") <=> (myRead[p] # NoRead)
  /\ \A p, q \in 1..N : (stage[p] = "reading" /\ stage[q] = "reading") => (p = q)

BeginRead(p) ==
  /\ stage[p] = "idle"
  /\ ~slow[p]
  /\ stage' = [stage EXCEPT ![p] = "reading"]
  /\ myRead' = [myRead EXCEPT ![p] = 0]
  /\ UNCHANGED slow

ReadStep(p) ==
  /\ stage[p] = "reading"
  /\ myRead[p] < MaxNat
  /\ myRead' = [myRead EXCEPT ![p] = myRead[p] + 1]
  /\ UNCHANGED <<stage, slow>>

Enter(p) ==
  /\ stage[p] = "reading"
  /\ myRead[p] = MaxNat
  /\ \A o \in 1..N \ {p} : stage[o] # "inCS"
  /\ stage' = [stage EXCEPT ![p] = "inCS"]
  /\ UNCHANGED <<myRead, slow>>

Exit(p) ==
  /\ stage[p] = "inCS"
  /\ stage' = [stage EXCEPT ![p] = "idle"]
  /\ myRead' = [myRead EXCEPT ![p] = NoRead]
  /\ UNCHANGED slow

ToggleSlowness(p) ==
  /\ slow' = [slow EXCEPT ![p] = ~slow[p]]
  /\ UNCHANGED <<stage, myRead>>

Next ==
  \E p \in 1..N :
    \/ BeginRead(p)
    \/ ReadStep(p)
    \/ Enter(p)
    \/ Exit(p)
    \/ ToggleSlowness(p)

Spec == Init /\ [][Next]_vars

TicketsWithinBounds ==
  \A p \in 1..N : myRead[p] <= MaxNat

====