---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES pc, wants, ticket, nextTicket

vars == <<pc, wants, ticket, nextTicket>>

Processes == 1..N
Range == 0..MaxNat

NatOverride(x) == x % (MaxNat + 1)

TypeOK ==
    /\ pc \in [Processes -> {"idle", "waiting", "critical", "exit"}]
    /\ wants \in [Processes -> BOOLEAN]
    /\ ticket \in [Processes -> Range]
    /\ nextTicket \in Range

MutualExclusion ==
    \A i \in Processes, j \in Processes :
        (pc[i] = "critical" /\ pc[j] = "critical") => i = j

Inv == TypeOK /\ MutualExclusion

Init ==
    /\ pc = [i \in Processes |-> "idle"]
    /\ wants = [i \in Processes |-> FALSE]
    /\ ticket = [i \in Processes |-> 0]
    /\ nextTicket = 0

Request(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "waiting"]
    /\ wants' = [wants EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = NatOverride(nextTicket + 1)

Enter(i) ==
    /\ pc[i] = "waiting"
    /\ \A j \in Processes : (wants[j] /\ j # i) => ticket[i] < ticket[j]
    /\ pc' = [pc EXCEPT ![i] = "critical"]
    /\ UNCHANGED <<wants, ticket, nextTicket>>

Leave(i) ==
    /\ pc[i] = "critical"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<wants, ticket, nextTicket>>

Reset(i) ==
    /\ pc[i] = "exit"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ wants' = [wants EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<ticket, nextTicket>>

Next ==
    \/ \E i \in Processes : Request(i)
    \/ \E i \in Processes : Enter(i)
    \/ \E i \in Processes : Leave(i)
    \/ \E i \in Processes : Reset(i)

ISpec == Init /\ [][Next]_vars

====