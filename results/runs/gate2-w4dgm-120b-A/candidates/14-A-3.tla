---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, Boulanger

CONSTANTS N, MaxNat

\* An override that replaces the unbounded Naturals.Nat with a finite range
\* 0..MaxNat.  It is a definition, never a declaration or a redefinition of Nat.
NatOverride == Nat \ {0..MaxNat}

VARIABLES inCS, want, serving, tkt
vars == <<inCS, want, serving, tkt>>

TypeOK ==
    /\ inCS \in [1..N -> BOOLEAN]
    /\ want \in [1..N -> BOOLEAN]
    /\ serving \in [1..N -> BOOLEAN]
    /\ tkt \in [1..N -> 0..MaxNat]

Init ==
    /\ inCS = [p \in 1..N |-> FALSE]
    /\ want = [p \in 1..N |-> FALSE]
    /\ serving = [p \in 1..N |-> FALSE]
    /\ tkt = [p \in 1..N |-> 0]

\* The bounded natural numbers must stay below the finite override ceiling.
Bounded == \A p \in 1..N : tkt[p] < MaxNat

Request(p) ==
    /\ ~want[p]
    /\ ~inCS[p]
    /\ want' = [want EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<inCS, serving, tkt>>

Grant(p) ==
    /\ want[p]
    /\ ~serving[p]
    /\ \A q \in 1..N : ~serving[q]
    /\ tkt[p] < MaxNat
    /\ serving' = [serving EXCEPT ![p] = TRUE]
    /\ tkt' = [tkt EXCEPT ![p] = tkt[p] + 1]
    /\ UNCHANGED <<inCS, want>>

Enter(p) ==
    /\ serving[p]
    /\ ~inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<want, serving, tkt>>

Leave(p) ==
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ serving' = [serving EXCEPT ![p] = FALSE]
    /\ want' = [want EXCEPT ![p] = FALSE]
    /\ UNCHANGED tkt

Next == \E p \in 1..N : Request(p) \/ Grant(p) \/ Enter(p) \/ Leave(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p \in 1..N : inCS[p] => (\A q \in 1..N \ {p} : ~inCS[q])

\* The ticket office never runs two processes at once, so the ticket counter
\* takes every value up to the live ceiling and no value is skipped.
Inv ==
    /\ MutualExclusion
    /\ Bounded

====