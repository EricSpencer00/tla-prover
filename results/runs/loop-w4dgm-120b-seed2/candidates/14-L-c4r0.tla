---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, FiniteSets, Boulanger

CONSTANTS N, MaxNat

StateSpace == {"idle", "trying", "critical", "exiting"}
Succ(x) == IF x = N - 1 THEN 0 ELSE x + 1

VARIABLES pc, ticket, owner, log, crashed

vars == <<pc, ticket, owner, log, crashed>>

TypeOK ==
    /\ pc \in [0 .. N - 1 -> StateSpace]
    /\ ticket \in [0 .. N - 1 -> 0 .. MaxNat]
    /\ owner \in 0 .. N - 1
    /\ log \in Seq(0 .. N - 1)
    /\ crashed \in SUBSET (0 .. N - 1)

Init ==
    /\ pc = [i \in 0 .. N - 1 |-> "idle"]
    /\ ticket = [i \in 0 .. N - 1 |-> 0]
    /\ owner = 0
    /\ log = << >>
    /\ crashed = {}

Begin(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "trying"]
    /\ UNCHANGED <<ticket, owner, log, crashed>>

ReadTicket(i) ==
    /\ pc[i] = "trying"
    /\ ticket' = [ticket EXCEPT ![i] = (ticket[owner] + 1) % (MaxNat + 1)]
    /\ UNCHANGED <<pc, owner, log, crashed>>

Enter(i) ==
    /\ pc[i] = "trying"
    /\ i = owner
    /\ \A j \in 0 .. N - 1 : pc[j] # "critical"
    /\ pc' = [pc EXCEPT ![i] = "critical"]
    /\ UNCHANGED <<ticket, owner, log, crashed>>

Exit(i) ==
    /\ pc[i] = "critical"
    /\ pc' = [pc EXCEPT ![i] = "exiting"]
    /\ UNCHANGED <<ticket, owner, log, crashed>>

Leave(i) ==
    /\ pc[i] = "exiting"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ owner' = Succ(i)
    /\ log' = Append(log, i)
    /\ UNCHANGED <<ticket, crashed>>

Crash(i) ==
    /\ i \notin crashed
    /\ crashed' = crashed \cup {i}
    /\ UNCHANGED <<pc, ticket, owner, log>>

Next ==
    \/ \E i \in 0 .. N - 1 : Begin(i)
    \/ \E i \in 0 .. N - 1 : ReadTicket(i)
    \/ \E i \in 0 .. N - 1 : Enter(i)
    \/ \E i \in 0 .. N - 1 : Exit(i)
    \/ \E i \in 0 .. N - 1 : Leave(i)
    \/ \E i \in 0 .. N - 1 : Crash(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    /\ \A i, j \in 0 .. N - 1 : (pc[i] = "critical" /\ pc[j] = "critical") => i = j
    /\ \A i \in 0 .. N - 1 : pc[i] = "critical" => i = owner

Inv ==
    /\ \A i \in 0 .. N - 1 : pc[i] \in StateSpace

TicketBound ==
    /\ \A i \in 0 .. N - 1 : ticket[i] <= MaxNat

====