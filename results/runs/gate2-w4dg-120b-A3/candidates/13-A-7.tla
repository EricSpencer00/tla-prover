---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES serving, ticket, quiet

vars == <<serving, ticket, quiet>>

TypeOK ==
  /\ serving \in [1..N -> {"idle", "waiting", "cs"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ quiet \in [1..N -> BOOLEAN]

MutualExclusion ==
  \A i, j \in 1..N : (i # j /\ serving[i] = "cs") => serving[j] # "cs"

Inv == MutualExclusion /\ TypeOK

Init ==
  /\ serving = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ quiet = [i \in 1..N |-> FALSE]

TakeTicket(i) ==
  /\ serving[i] = "idle"
  /\ serving' = [serving EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] = MaxNat]
  /\ quiet' = [quiet EXCEPT ![i] = FALSE]

Enter(i) ==
  /\ serving[i] = "waiting"
  /\ \A j \in 1..N : (serving[j] # "cs") \/ (ticket[j] > ticket[i])
  /\ serving' = [serving EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<ticket, quiet>>

Exit(i) ==
  /\ serving[i] = "cs"
  /\ serving' = [serving EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED <<quiet>>

Stall(i) ==
  /\ serving[i] = "cs"
  /\ quiet' = [quiet EXCEPT ![i] = ~quiet[i]]
  /\ UNCHANGED <<serving, ticket>>

Next ==
  \E i \in 1..N :
    \/ TakeTicket(i)
    \/ Enter(i)
    \/ Exit(i)
    \/ Stall(i)

ISpec == Init /\ [][Next]_vars

====