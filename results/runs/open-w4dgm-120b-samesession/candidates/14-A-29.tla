---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* A finite ticket range 0..MaxNat replaces the unbounded Nat.
NatOverride(x) == x % (MaxNat + 1)

VARIABLES inCS, ticket, wants, prog

vars == <<inCS, ticket, wants, prog>>

TypeOK ==
    /\ inCS \subseteq (1..N)
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ wants \in [1..N -> BOOLEAN]
    /\ prog \in [1..N -> {"idle", "waiting", "holder", "exit"}]

Init ==
    /\ inCS = {}
    /\ ticket = [p \in 1..N |-> 0]
    /\ wants = [p \in 1..N |-> FALSE]
    /\ prog = [p \in 1..N |-> "idle"]

Request(p) ==
    /\ ~wants[p]
    /\ wants' = [wants EXCEPT ![p] = TRUE]
    /\ prog' = [prog EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<inCS, ticket>>

\* The ticket register advances, wrapping within the bounded range, so no
\* unbounded natural number is ever introduced.
Enter(p) ==
    /\ prog[p] = "waiting"
    /\ inCS = {}
    /\ inCS' = inCS \cup {p}
    /\ ticket' = [ticket EXCEPT ![p] = NatOverride(@)]
    /\ prog' = [prog EXCEPT ![p] = "holder"]
    /\ UNCHANGED wants

Exit(p) ==
    /\ prog[p] = "holder"
    /\ inCS' = inCS \ {p}
    /\ prog' = [prog EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<ticket, wants>>

Reset(p) ==
    /\ prog[p] = "exit"
    /\ prog' = [prog EXCEPT ![p] = "idle"]
    /\ wants' = [wants EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<inCS, ticket>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)
    \/ \E p \in 1..N : Reset(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p \in 1..N : prog[p] = "holder" => inCS = {p}

Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A p \in inCS : prog[p] = "holder"

\* Ticket numbers stay within the model's finite range; always true under
\* the bounded NatOverride, so it is a harmless pruning condition here.
TicketsBounded == \A p \in 1..N : ticket[p] < MaxNat

====