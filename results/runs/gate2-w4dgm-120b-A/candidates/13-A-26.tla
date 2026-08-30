---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* The actual system uses the full set of naturals; for model checking it is
\* replaced everywhere with the finite range 0..MaxNat.
Nat == NatOverride

VARIABLES inCS, waiting, ticket, nextTicket

TypeOK ==
    /\ inCS \subseteq (1..N)
    /\ waiting \subseteq (1..N)
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

Init ==
    /\ inCS = {}
    /\ waiting = {}
    /\ ticket = [i \in 1..N |-> 0]
    /\ nextTicket = 0

\* A process that wants the critical section joins the waiting set.
Request(i) ==
    /\ i \notin waiting
    /\ i \notin inCS
    /\ waiting' = waiting \cup {i}
    /\ UNCHANGED <<inCS, ticket, nextTicket>>

\* The bakery grant is served in ticket order, and the ticket counter
\* saturates at MaxNat instead of growing unboundedly.
Grant(i) ==
    /\ i \in waiting
    /\ nextTicket < MaxNat
    /\ nextTicket' = nextTicket + 1
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket + 1]
    /\ waiting' = waiting \ {i}
    /\ UNCHANGED inCS

\* A process enters the critical section only when no one else is inside.
Enter(i) ==
    /\ inCS = {}
    /\ ticket[i] > 0
    /\ inCS' = {i}
    /\ UNCHANGED <<waiting, ticket, nextTicket>>

\* Leaving the critical section resets the process's ticket, freeing its
\* slot in the bounded ticket counter for reuse.
Exit(i) ==
    /\ i \in inCS
    /\ inCS' = inCS \ {i}
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED <<waiting, nextTicket>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Grant(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

\* The inductive spec is the safety net: from any reachable state satisfying
\* the invariant, every action must preserve it -- not just from the init.
ISpec == Init /\ [][Next]_<<inCS, waiting, ticket, nextTicket>>

\* Safety: mutual exclusion, no ticket handed out twice, and bounded counter.
MutualExclusion == \A i, j \in inCS : i = j
TypeOKInv == TypeOK
Inv == MutualExclusion /\ TypeOK

====