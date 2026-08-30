---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* Overrides the built-in Nat to a finite range; kept separate so the name "Nat"
\* from Naturals is never re-declared or hidden.
NatOverride == 0..MaxNat

VARIABLES holder, wants, inCS, tickets

vars == <<holder, wants, inCS, tickets>>

Nxt(p) == (p + 1) % N

TypeOK ==
    /\ holder \in 0..N-1
    /\ wants \subseteq 0..N-1
    /\ inCS \subseteq 0..N-1
    /\ tickets \in [0..N-1 -> NatOverride]

\* The invariant is the same shape as in the Boulanger specification; the
\* ticket comparison is what keeps the pairwise ordering equivalent to the ring order.
Inv ==
    /\ \A a, b \in inCS : a = b
    /\ \A p \in 1..N-1 : (p \in inCS) => (Nxt(p - 1) \in inCS)
    /\ \A a \in inCS, b \in wants : tickets[a] <= tickets[b]

Init ==
    /\ holder = 0
    /\ wants = {}
    /\ inCS = {}
    /\ tickets = [p \in 0..N-1 |-> 0]

Request(p) ==
    /\ p \notin wants
    /\ p \notin inCS
    /\ tickets[p] < MaxNat
    /\ wants' = wants \cup {p}
    /\ tickets' = [tickets EXCEPT ![p] = tickets[p] + 1]
    /\ UNCHANGED <<holder, inCS>>

Enter(p) ==
    /\ holder = p
    /\ p \in wants
    /\ inCS' = inCS \cup {p}
    /\ wants' = wants \ {p}
    /\ UNCHANGED <<holder, tickets>>

Exit(p) ==
    /\ p \in inCS
    /\ inCS' = inCS \ {p}
    /\ UNCHANGED <<holder, wants, tickets>>

PassToken ==
    /\ holder \notin inCS
    /\ holder' = Nxt(holder)
    /\ UNCHANGED <<wants, inCS, tickets>>

Next ==
    \/ \E p \in 0..N-1 : Request(p)
    \/ \E p \in 0..N-1 : Enter(p)
    \/ \E p \in 0..N-1 : Exit(p)
    \/ PassToken

Spec == Init /\ [][Next]_vars

MutualExclusion == \A a, b \in inCS : a = b
StateConstraint == \A p \in 0..N-1 : tickets[p] < MaxNat
====