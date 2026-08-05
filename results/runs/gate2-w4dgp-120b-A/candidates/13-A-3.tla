---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, chosen, ticket, maxTicket

vars == <<inCS, chosen, ticket, maxTicket>>

Proc == 1..N

RECURSIVE MaxTicket(_)
MaxTicket(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : \A z \in S : y >= z
         IN IF ticket[x] > MaxTicket(S \ {x}) THEN ticket[x] ELSE MaxTicket(S \ {x})

UNRECURSIVE MaxTicket(_)

Init ==
    /\ inCS = [p \in Proc |-> FALSE]
    /\ chosen = [p \in Proc |-> FALSE]
    /\ ticket = [p \in Proc |-> 0]
    /\ maxTicket = 0

Choose(p) ==
    /\ ~chosen[p]
    /\ ~inCS[p]
    /\ chosen' = [chosen EXCEPT ![p] = TRUE]
    /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket
    /\ ticket' = [ticket EXCEPT ![p] = maxTicket']
    /\ UNCHANGED inCS

Enter(p) ==
    /\ chosen[p]
    /\ ~inCS[p]
    /\ \A q \in Proc : (chosen[q] /\ ticket[q] < ticket[p]) => inCS[q] = FALSE
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<chosen, ticket, maxTicket>>

Exit(p) ==
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ chosen' = [chosen EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<ticket, maxTicket>>

Next ==
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Enter(p)
    \/ \E p \in Proc : Exit(p)

ISpec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p, q \in Proc : (inCS[p] /\ inCS[q]) => p = q

TypeOK ==
    /\ inCS \in [Proc -> BOOLEAN]
    /\ chosen \in [Proc -> BOOLEAN]
    /\ ticket \in [Proc -> 0..MaxNat]
    /\ maxTicket \in 0..MaxNat

Inv ==
    /\ \A p \in Proc : chosen[p] => (inCS[p] \/ ticket[p] <= maxTicket)
    /\ \A p \in Proc : inCS[p] => chosen[p]
    /\ \A p, q \in Proc : (chosen[p] /\ inCS[q] /\ ticket[p] < ticket[q]) => p = q

====