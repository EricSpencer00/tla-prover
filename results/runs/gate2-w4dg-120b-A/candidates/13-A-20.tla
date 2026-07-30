---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

RECURSIVE MaxNatOf(_)
MaxNatOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN IF x > MaxNatOf(S \ {x}) THEN x ELSE MaxNatOf(S \ {x})

\* The Bakery model: a ticket register whose values are now bounded.
VARIABLES inCS, ticket, waiting, served

vars == << inCS, ticket, waiting, served >>

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ waiting \subseteq (1..N)
  /\ served \subseteq (1..N)

MutualExclusion ==
  \A a, b \in 1..N : (inCS[a] /\ inCS[b]) => a = b

NoTicketInfoLost ==
  /\ \A p \in waiting : ticket[p] > 0
  /\ \A p \in 1..N : inCS[p] => p \in served

Inv == /\ TypeOK
       /\ MutualExclusion
       /\ NoTicketInfoLost

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ waiting = {}
  /\ served = {}

Request(p) ==
  /\ p \notin waiting
  /\ ~inCS[p]
  /\ p \notin served
  /\ waiting' = waiting \cup {p}
  /\ ticket' = [ticket EXCEPT ![p] = 1 + MaxNatOf({ticket[q] : q \in waiting \cup {p}})]
  /\ UNCHANGED << inCS, served >>

Enter(p) ==
  /\ p \in waiting
  /\ \A q \in waiting : ticket[p] <= ticket[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ waiting' = waiting \ {p}
  /\ UNCHANGED << ticket, served >>

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ served' = served \cup {p}
  /\ UNCHANGED waiting

Next == \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars

ISpec == Spec /\ WF_vars(Next)

====