---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS
    N, MaxNat

None == 0 - 1

VARIABLES inCS, entering, ticket, nextTicket
vars == <<inCS, entering, ticket, nextTicket>>

Nat == 0 .. MaxNat

TypeOK ==
    /\ inCS \subseteq 1 .. N
    /\ entering \subseteq 1 .. N
    /\ ticket \in [1 .. N -> Nat]
    /\ nextTicket \in Nat

Recur == { x \in Nat : x <= MaxNat }

MutualExclusion == \A p, q \in inCS : p = q

Inv ==
    /\ MutualExclusion
    /\ Recur
    /\ TypeOK

Init ==
    /\ inCS = {}
    /\ entering = {}
    /\ ticket = [p \in 1 .. N |-> None]
    /\ nextTicket = 0

Enter(p) ==
    /\ p \notin inCS
    /\ p \notin entering
    /\ entering' = entering \cup {p}
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = (nextTicket + 1) % (MaxNat + 1)
    /\ UNCHANGED inCS

EnterCritical(p) ==
    /\ p \in entering
    /\ \A q \in entering : ticket[q] < ticket[p]
    /\ entering' = entering \ {p}
    /\ inCS' = inCS \cup {p}
    /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
    /\ p \in inCS
    /\ inCS' = inCS \ {p}
    /\ ticket' = [ticket EXCEPT ![p] = None]
    /\ UNCHANGED <<entering, nextTicket>>

Next ==
    \/ \E p \in 1 .. N : Enter(p)
    \/ \E p \in 1 .. N : EnterCritical(p)
    \/ \E p \in 1 .. N : Exit(p)

ISpec == Init /\ [][Next]_vars

====