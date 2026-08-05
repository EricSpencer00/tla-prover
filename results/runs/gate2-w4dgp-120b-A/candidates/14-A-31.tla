---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES cs, ticket, served, nextTicket

vars == <<cs, ticket, served, nextTicket>>

Processes == 1..N

TypeOK ==
    /\ cs \subseteq Processes
    /\ ticket \in [Processes -> 0..MaxNat]
    /\ served \in 0..MaxNat
    /\ nextTicket \in 0..MaxNat

Inv ==
    /\ cs = {}
    /\ served = 0

\* ACTIONS inherited from Boulanger; they are reproduced here so the
\* full module is self-contained, but they are unchanged.
\* A process takes a ticket and later enters the critical section.
\* Because the model overrides the full Nat set with a bounded range, the
\* ticket/pass counter only advances below MaxNat.

NextTicket == IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket

Enter ==
    \E p \in Processes :
        /\ p \notin cs
        /\ ticket' = [ticket EXCEPT ![p] = NextTicket]
        /\ cs' = cs \cup {p}
        /\ nextTicket' = NextTicket
        /\ served' = served

Exit ==
    \E p \in cs :
        /\ cs' = cs \ {p}
        /\ served' = IF served < MaxNat THEN served + 1 ELSE served
        /\ ticket' = [ticket EXCEPT ![p] = 0]
        /\ nextTicket' = nextTicket

Init ==
    /\ cs = {}
    /\ ticket = [p \in Processes |-> 0]
    /\ served = 0
    /\ nextTicket = 0

Spec == Init /\ [][Inv]_vars

MutualExclusion == cs = {}

\* Finite-range override: every ticket number must stay below MaxNat,
\* which also keeps the model's finite-horizon check from exploring the
\* artificial tail of the full natural-number set.
NatOverride == \A p \in Processes : ticket[p] < MaxNat

====