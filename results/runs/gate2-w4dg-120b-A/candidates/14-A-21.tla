---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* Boulanger's mutual exclusion scheme with a capped natural number range.
\* A state constraint keeps ticket numbers below the maximum.

VARIABLES pc, tickets, glb

vars == <<pc, tickets, glb>>

TypeOK ==
    /\ pc \in [1..N -> {"idle", "trying", "critical"}]
    /\ tickets \in [1..N -> 0..MaxNat]
    /\ glb \in 0..MaxNat

MutualExclusion ==
    \A i \in 1..N : pc[i] = "critical" => \A j \in 1..N : (j # i) => pc[j] # "critical"

Init ==
    /\ pc = [i \in 1..N |-> "idle"]
    /\ tickets = [i \in 1..N |-> 0]
    /\ glb = 0

Try(i) ==
    /\ pc[i] = "idle"
    /\ glb < MaxNat
    /\ tickets' = [tickets EXCEPT ![i] = glb]
    /\ glb' = glb + 1
    /\ pc' = [pc EXCEPT ![i] = "trying"]

Enter(i) ==
    /\ pc[i] = "trying"
    /\ \A j \in 1..N : (j # i /\ pc[j] = "critical") => tickets[i] < tickets[j]
    /\ pc' = [pc EXCEPT ![i] = "critical"]
    /\ UNCHANGED <<tickets, glb>>

Exit(i) ==
    /\ pc[i] = "critical"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<tickets, glb>>

Next ==
    \E i \in 1..N :
        \/ Try(i)
        \/ Enter(i)
        \/ Exit(i)

TicketsBelowBound == \A i \in 1..N : tickets[i] < MaxNat

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ MutualExclusion

====