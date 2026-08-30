---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, wants, ticket, nextTicket, crashed

vars == <<inCS, wants, ticket, nextTicket, crashed>>

\* Overridden bounded version of the natural-number type for model checking.
NatOverride == 0 .. MaxNat

TypeOK ==
    /\ inCS \subseteq 1..N
    /\ wants \subseteq 1..N
    /\ ticket \in [1..N -> NatOverride]
    /\ nextTicket \in NatOverride
    /\ crashed \subseteq 1..N

\* The bakery invariant: the critical-section occupant set is contained in the
\* currently-wanting set, so no unauthorized or stale process ever enters.
Inv == inCS \subseteq wants

MutualExclusion == \A i, j \in inCS : i = j

Init ==
    /\ inCS = {}
    /\ wants = {}
    /\ ticket = [i \in 1..N |-> 0]
    /\ nextTicket = 0
    /\ crashed = {}

Request(i) ==
    /\ i \notin wants
    /\ i \notin inCS
    /\ i \notin crashed
    /\ wants' = wants \cup {i}
    /\ UNCHANGED <<inCS, ticket, nextTicket, crashed>>

\* Takes the next free ticket, wrapping within the bounded model-checking range.
TakeTicket(i) ==
    /\ i \in wants
    /\ ticket[i] = 0
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = IF nextTicket = MaxNat THEN 0 ELSE nextTicket + 1
    /\ UNCHANGED <<inCS, wants, crashed>>

\* Entry requires holding the lowest ticket among all wanters, and never admits
\* an already-crashed process.
Enter(i) ==
    /\ i \in wants
    /\ i \notin inCS
    /\ i \notin crashed
    /\ \A j \in wants : ticket[i] <= ticket[j]
    /\ inCS' = inCS \cup {i}
    /\ UNCHANGED <<wants, ticket, nextTicket, crashed>>

Leave(i) ==
    /\ i \in inCS
    /\ inCS' = inCS \ {i}
    /\ wants' = wants \ {i}
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED <<nextTicket, crashed>>

Crash(i) ==
    /\ i \notin crashed
    /\ crashed' = crashed \cup {i}
    /\ inCS' = inCS \ {i}
    /\ wants' = wants \ {i}
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED nextTicket

Recover(i) ==
    /\ i \in crashed
    /\ crashed' = crashed \ {i}
    /\ UNCHANGED <<inCS, wants, ticket, nextTicket>>

Next ==
    \E i \in 1..N :
        \/ Request(i)
        \/ TakeTicket(i)
        \/ Enter(i)
        \/ Leave(i)
        \/ Crash(i)
        \/ Recover(i)

Spec == Init /\ [][Next]_vars

ISpec == Spec

====