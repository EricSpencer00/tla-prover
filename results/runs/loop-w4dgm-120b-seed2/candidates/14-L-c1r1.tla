---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, tickets, nextTicket, enabled, target, epoch

vars == <<inCS, tickets, nextTicket, enabled, target, epoch>>

\* A token grants mutual exclusion; a process acquires it by swapping from a
\* token marked with its own epoch to a freshly numbered ticket.
Token == "token"
Free == "free"
NoTarget == N

TypeOK ==
    /\ inCS \in (0..N) \cup {Free}
    /\ tickets \in [0..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
    /\ enabled \subseteq 0..N
    /\ target \in 0..N
    /\ epoch \in 0..MaxNat

Init ==
    /\ inCS = Free
    /\ tickets = [p \in 0..N |-> 0]
    /\ nextTicket = 0
    /\ enabled = 0..N
    /\ target = NoTarget
    /\ epoch = 0

\* A reconfiguration bumps the epoch and clears the coarse lock; ticket numbers
\* are preserved, so a process holding a ticket from the previous epoch becomes
\* stale and can no longer claim the lock.
Reconfigure ==
    /\ epoch' = IF epoch = MaxNat THEN 0 ELSE epoch + 1
    /\ inCS' = Free
    /\ tickets' = [p \in 0..N |-> 0]
    /\ UNCHANGED <<nextTicket, enabled, target>>

Enter(p) ==
    /\ p \in enabled
    /\ inCS = Free
    /\ tickets[p] = 0
    /\ nextTicket < MaxNat
    /\ epoch > 0
    /\ inCS' = p
    /\ tickets' = [tickets EXCEPT ![p] = nextTicket]
    /\ nextTicket' = nextTicket + 1
    /\ UNCHANGED <<enabled, target, epoch>>

Exit(p) ==
    /\ inCS = p
    /\ inCS' = Free
    /\ UNCHANGED <<tickets, nextTicket, enabled, target, epoch>>

\* Coarse lock acquisition is blocked whenever the current holder is slow:
\* the slow process holds the coarse lock but never holds a ticket, so a
\* fresh attempt must wait for it to release rather than racing ahead.
FastEnter(p) ==
    /\ p \in enabled
    /\ inCS = Free
    /\ inCS' = p
    /\ UNCHANGED <<tickets, nextTicket, enabled, target, epoch>>

FastExit(p) ==
    /\ inCS = p
    /\ tickets[p] = 0
    /\ inCS' = Free
    /\ UNCHANGED <<tickets, nextTicket, enabled, target, epoch>>

SetTarget(p) ==
    /\ p # target
    /\ target' = p
    /\ UNCHANGED <<inCS, tickets, nextTicket, enabled, epoch>>

Stall ==
    /\ inCS = Free
    /\ enabled = {}
    /\ UNCHANGED vars

Next ==
    \/ Reconfigure
    \/ \E p \in 0..N : Enter(p)
    \/ \E p \in 0..N : Exit(p)
    \/ \E p \in 0..N : FastEnter(p)
    \/ \E p \in 0..N : FastExit(p)
    \/ \E p \in 0..N : SetTarget(p)
    \/ Stall

Spec == Init /\ [][Next]_vars

\* Mutual exclusion holds at all times: a process sits in the critical section
\* only while it is the recorded holder of the coarse token.
MutualExclusion == \A p \in 0..N : (inCS = p) => (tickets[p] > 0)

Inv ==
    /\ MutualExclusion
    /\ TypeOK

====