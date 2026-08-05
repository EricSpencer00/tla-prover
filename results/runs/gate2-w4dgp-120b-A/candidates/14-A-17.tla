---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat

\* The Boulanger algorithm's shared variables (inherited from the standard
\* Boulanger mutual exclusion model). Each process has a state, a ticket,
\* and a request flag; the lock register holds the current holder.
VARIABLES pstate, ticket, request, lock

vars == <<pstate, ticket, request, lock>>

States == {"idle", "trying", "critical"}

TypeOK ==
    /\ pstate \in [1..N -> States]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ request \in [1..N -> BOOLEAN]
    /\ lock \in 0..N

Init ==
    /\ pstate = [p \in 1..N |-> "idle"]
    /\ ticket = [p \in 1..N |-> 0]
    /\ request = [p \in 1..N |-> FALSE]
    /\ lock = 0

\* A process requests entry into the critical section.
Request(p) ==
    /\ ~ request[p]
    /\ pstate[p] = "idle"
    /\ request' = [request EXCEPT ![p] = TRUE]
    /\ pstate' = [pstate EXCEPT ![p] = "trying"]
    /\ UNCHANGED <<ticket, lock>>

\* The process picks a ticket number on entering the queue. Bounded by the
\* model's finite Nat override: only pick a ticket if it's below MaxNat.
Pick(p) ==
    /\ pstate[p] = "trying"
    /\ ticket[p] = 0
    /\ \E t \in 1..MaxNat :
        /\ ticket' = [ticket EXCEPT ![p] = t]
    /\ UNCHANGED <<pstate, request, lock>>

\* Enter the critical section when the lock is free and the ticket ordering
\* is respected: any process ahead of us must already have been served.
Enter(p) ==
    /\ pstate[p] = "trying"
    /\ ticket[p] # 0
    /\ lock = 0
    /\ \A j \in 1..N :
        (pstate[j] = "critical" /\ ticket[j] < ticket[p]) => FALSE
    /\ lock' = p
    /\ pstate' = [pstate EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<ticket, request>>

\* Exit the critical section.
Exit(p) ==
    /\ pstate[p] = "critical"
    /\ pstate' = [pstate EXCEPT ![p] = "idle"]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ request' = [request EXCEPT ![p] = FALSE]
    /\ lock' = 0

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Pick(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..N : Request(p) \/ Pick(p) \/ Enter(p) \/ Exit(p))

\* Mutual exclusion: nobody else holds the lock while a process is in its
\* critical section.
MutualExclusion ==
    \A p \in 1..N : pstate[p] = "critical" => lock = p

\* The operational invariant from the Boulanger base specification: while a
\* process is in its critical section its ticket equals the lock register.
Inv ==
    \A p \in 1..N : pstate[p] = "critical" => ticket[p] = lock

\* State constraint: keep every ticket below MaxNat so the finite Nat override
\* never forces an out-of-range ticket into an explored state.
NatBound == \A p \in 1..N : ticket[p] < MaxNat

NatOverride == Nat

====