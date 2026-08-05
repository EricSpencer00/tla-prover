---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

ASSUME MaxNat \in Nat

VARIABLES ticket, entering, c

vars == <<ticket, entering, c>>

MaxTicket == MaxNat

\* Replaces the infinite Nat with a finite range 0..MaxNat so ticket numbers
\* stay within a bounded set.  The full Naturals module is still extended for
\* other operators that are not overridden.
Nat(n) == IF n > MaxNat THEN MaxNat ELSE n

TypeOK ==
    /\ ticket \in [1..N -> 0..MaxTicket]
    /\ entering \in [1..N -> {"idle", "waiting", "critical"}]
    /\ c \in 0..1

Init ==
    /\ ticket = [p \in 1..N |-> 0]
    /\ entering = [p \in 1..N |-> "idle"]
    /\ c = 0

Request(p) ==
    /\ entering[p] = "idle"
    /\ entering' = [entering EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<ticket, c>>

Acquire(p) ==
    /\ entering[p] = "waiting"
    /\ \A q \in 1..N : entering[q] # "critical" /\ ticket[q] > ticket[p]
    /\ entering' = [entering EXCEPT ![p] = "critical"]
    /\ ticket' = [ticket EXCEPT ![p] = Nat(ticket[p] + 1)]
    /\ UNCHANGED c

Enter(p) ==
    /\ entering[p] = "critical"
    /\ c = 0
    /\ c' = 1
    /\ UNCHANGED <<ticket, entering>>

Exit(p) ==
    /\ entering[p] = "critical"
    /\ c = 1
    /\ c' = 0
    /\ entering' = [entering EXCEPT ![p] = "idle"]
    /\ UNCHANGED ticket

Next ==
    \E p \in 1..N :
        \/ Request(p)
        \/ Acquire(p)
        \/ Enter(p)
        \/ Exit(p)

Next_ == Next

MutualExclusion ==
    \A p \in 1..N : entering[p] = "critical" => c = 1

Inv ==
    /\ TypeOK
    /\ MutualExclusion
    /\ \A p \in 1..N : entering[p] \in {"idle", "waiting", "critical"}
    /\ c \in {0, 1}

ISpec == Init /\ [][Next]_vars

====